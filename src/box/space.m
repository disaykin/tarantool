/*
 * Redistribution and use in source and binary forms, with or
 * without modification, are permitted provided that the following
 * conditions are met:
 *
 * 1. Redistributions of source code must retain the above
 *    copyright notice, this list of conditions and the
 *    following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials
 *    provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY <COPYRIGHT HOLDER> ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
 * <COPYRIGHT HOLDER> OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */
#include "space.h"
#include <stdlib.h>
#include <string.h>
#include <cfg/tarantool_box_cfg.h>
#include <cfg/warning.h>
#include <tarantool.h>
#include <exception.h>
#include "tuple.h"
#include <pickle.h>
#include <palloc.h>
#include <assoc.h>

const char *field_data_type_strs[] = {"UNKNOWN", "NUM", "NUM64", "STR", "\0"};

static struct mh_i32ptr_t *spaces;

bool secondary_indexes_enabled = false;
bool primary_indexes_enabled = false;

struct space *
space_create(u32 space_no, u32 arity_min, u32 arity_max)
{
	struct space *space = space_by_n(space_no);
	if (space)
		panic("Space %d is already exists", space_no);
	space = calloc(1, sizeof(struct space));
	space->no = space_no;

	const struct mh_i32ptr_node_t node = { .key = space->no, .val = space };
	mh_i32ptr_put(spaces, &node, NULL, NULL, NULL);

	assert (space->arity_min <= space->arity_max);
	space->arity_min = arity_min;
	space->arity_max = arity_max;

	space->field_defs = NULL;
	space->fields_defs_capacity = 0;

	return space;
}

void
space_destroy(struct space *space)
{
	const struct mh_i32ptr_node_t node = { .key = space->no };
	mh_int_t h = mh_i32ptr_get(spaces, &node, NULL, NULL);

	int j;
#if defined(DEBUG)
	Index *pk = space->index[0];
	struct iterator *it = pk->position;
	struct tuple *tuple;
	[pk initIterator: it :ITER_ALL :NULL :0];
	while ((tuple = it->next(it))) {
		tuple->refs = 0;
		tuple_free(tuple);
	}
#endif /* defined(DEBUG) */
	for (j = 0 ; j < space->index_count; j++) {
		Index *index = space->index[j];
		[index free];
	}

	if (space->field_defs != NULL) {
		free(space->field_defs);
	}
	free(space);

	mh_i32ptr_del(spaces, h, NULL, NULL);
}

void
space_set_field_def(struct space *sp, u32 field_no,
		    const struct field_def *field_def)
{
	/* check that the space is empty */
	if (sp->index_count > 0 && [sp->index[0] size] == 0)
		panic("Space %d: is not empty", sp->no);

	if (field_no >= sp->arity_max) {
		panic("Space %d: field %u does not match space arity (%u)",
		      sp->no, field_no, sp->arity_max);
	}

	if (field_no >= sp->fields_defs_capacity) {
		size_t capacity = 2;
		while (field_no >= capacity)
			capacity *= 2;

		capacity = MIN(sp->arity_max, capacity);

		sp->field_defs = realloc(sp->field_defs,
			capacity  * sizeof(*sp->field_defs));
		assert (sp->field_defs != NULL);

		memset(sp->field_defs + sp->fields_defs_capacity, 0,
			sizeof(*sp->field_defs) * (capacity - sp->fields_defs_capacity));

		sp->fields_defs_capacity = capacity;
	}

	if (sp->field_defs[field_no].type != UNKNOWN &&
			memcmp(&sp->field_defs[field_no], field_def, sizeof(*field_def)) != 0) {
		panic("Space %d: field %u is already defined with different type",
		      sp->no, field_no);
	}

	sp->field_defs[field_no] = *field_def;

	if (field_no >= sp->arity_min) {
		sp->arity_min = field_no + 1;
	}
}

u32
space_create_index(struct space *sp, enum index_type type,
		   const struct key_def *key_def)
{
	if (sp->index_count >= BOX_INDEX_MAX) {
		panic("Space %u: too many indexes", sp->no);
	}

	/* check that the space is empty */
	if (sp->index_count > 0 && [sp->index[0] size] > 0)
		panic("Space %d: is not empty", sp->no);

	/* Check that all index fields is defined */
	for (u32 part = 0; part < key_def->part_count; part++) {
		u32 field_no = key_def->parts[part];
		if (field_no >= sp->arity_min ||
		    sp->field_defs[field_no].type == UNKNOWN) {
			panic("Space %u: field %u is not defined",
			      sp->no, field_no);
		}
	}

	Index *index = [[Index alloc :type :key_def :sp]
			init :key_def :sp];
	assert (index != NULL);

	u32 index_no = sp->index_count++;
	sp->index[index_no] = index;
	sp->index_type[index_no] = type;
	return index_no;
}

/** Get index ordinal number in space. */
i32
index_n(Index *index)
{
	for (i32 index_no = 0; index_no < index->space->index_count; index_no++) {
		if (index == index->space->index[index_no]) {
			return index_no;
		}
	}

	assert(false);
	return -1;
}

/* return space by its number */
struct space *
space_by_n(u32 n)
{
	const struct mh_i32ptr_node_t node = { .key = n };
	mh_int_t space = mh_i32ptr_get(spaces, &node, NULL, NULL);
	if (space == mh_end(spaces))
		return NULL;
	return mh_i32ptr_node(spaces, space)->val;
}

/** Return the number of active indexes in a space. */
static inline int
index_count(struct space *sp)
{
	if (!secondary_indexes_enabled) {
		/* If secondary indexes are not enabled yet,
		   we can use only the primary index. So return
		   1 if there is at least one index (which
		   must be primary) and return 0 otherwise. */
		return sp->index_count > 0;
	} else {
		/* Return the actual number of indexes. */
		return sp->index_count;
	}
}

/**
 * Visit all enabled spaces and apply 'func'.
 */
void
space_foreach(void (*func)(struct space *sp, void *udata), void *udata) {

	mh_int_t i;
	mh_foreach(spaces, i) {
		struct space *space = mh_i32ptr_node(spaces, i)->val;
		func(space, udata);
	}
}

struct tuple *
space_replace(struct space *sp, struct tuple *old_tuple,
	      struct tuple *new_tuple, enum dup_replace_mode mode)
{
	int i = 0;
	@try {
		/* Update the primary key */
		Index *pk = sp->index[0];
		assert(pk->key_def.is_unique);
		/*
		 * If old_tuple is not NULL, the index
		 * has to find and delete it, or raise an
		 * error.
		 */
		old_tuple = [pk replace: old_tuple :new_tuple :mode];

		assert(old_tuple || new_tuple);
		int n = index_count(sp);
		/* Update secondary keys */
		for (i = i + 1; i < n; i++) {
			Index *index = sp->index[i];
			[index replace: old_tuple :new_tuple :DUP_INSERT];
		}
		return old_tuple;
	} @catch (tnt_Exception *e) {
		/* Rollback all changes */
		for (i = i - 1; i >= 0;  i--) {
			Index *index = sp->index[i];
			[index replace: new_tuple: old_tuple: DUP_INSERT];
		}
		@throw;
	}
}

void
space_validate_tuple(struct space *sp, struct tuple *new_tuple)
{
	/* Check to see if the tuple has a sufficient number of fields. */
	if (new_tuple->field_count < sp->arity_min ||
			new_tuple->field_count > sp->arity_max)
		tnt_raise(IllegalParams, :"tuple arity must match space arity");

	/* Sweep through the tuple and check the field sizes. */
	u8 *data = new_tuple->data;
	for (u32 field_no = 0; field_no < sp->arity_min; field_no++) {
		/* Get the size of the current field and advance. */
		u32 field_size = load_varint32((const void **) &data);
		data += field_size;
		/*
		 * Check fixed size fields (NUM and NUM64) and
		 * skip undefined size fields (STRING and UNKNOWN).
		 */

		struct field_def *field_def = &sp->field_defs[field_no];
		if (field_def->type == NUM && field_size != sizeof(u32)) {
			tnt_raise(ClientError, :ER_KEY_FIELD_SIZE,
				  sp->no, field_no,
				  sizeof(u32), field_size);
		}

		if (field_def->type == NUM64 && field_size != sizeof(u64)) {
			tnt_raise(ClientError, :ER_KEY_FIELD_SIZE,
				  sp->no,
				  field_no, sizeof(u64), field_size);
		}
	}
}

void
space_free(void)
{
	mh_int_t i;

	mh_foreach(spaces, i) {
		struct space *space = mh_i32ptr_node(spaces, i)->val;
		space_destroy(space);
	}

}

/**
 * Extract all available field info from keys
 */
static void
space_init_field_defs(struct space *sp, tarantool_cfg_space *cfg_space)
{
	for (int j = 0; cfg_space->index[j] != NULL; ++j) {
		typeof(cfg_space->index[j]) cfg_index = cfg_space->index[j];

		for (int k = 0; cfg_index->key_field[k] != NULL; ++k) {
			typeof(cfg_index->key_field[k]) cfg_key =
					cfg_index->key_field[k];

			if (cfg_key->fieldno == -1) {
				/* last filled key reached */
				break;
			}

			enum field_data_type type = STR2ENUM(field_data_type,
							     cfg_key->type);

			struct field_def def = {
				.type = type
			};

			space_set_field_def(sp, cfg_key->fieldno, &def);
		}
	}
}

static void
space_init_index(struct space *sp, tarantool_cfg_space_index *cfg_index)
{
	enum index_type type = STR2ENUM(index_type, cfg_index->type);

	struct key_def key_def;

	key_def.part_count = 0;
	for (u32 k = 0; cfg_index->key_field[k] != NULL; ++k) {
		typeof(cfg_index->key_field[k]) cfg_key =
				cfg_index->key_field[k];

		if (cfg_key->fieldno == -1) {
			/* last filled key reached */
			break;
		}

		key_def.part_count++;
	}

	for (u32 k = 0; k < key_def.part_count; ++k) {
		typeof(cfg_index->key_field[k]) cfg_key =
				cfg_index->key_field[k];
		key_def.parts[k] = cfg_key->fieldno;
	}

	key_def.is_unique = cfg_index->unique;
	space_create_index(sp, type, &key_def);

	return;
}

static void
space_config()
{
	/* exit if no spaces are configured */
	if (cfg.space == NULL) {
		return;
	}

	/* fill box spaces */
	for (u32 space_no = 0; cfg.space[space_no] != NULL; ++space_no) {
		tarantool_cfg_space *cfg_space = cfg.space[space_no];

		if (!CNF_STRUCT_DEFINED(cfg_space) || !cfg_space->enabled)
			continue;

		assert(cfg.memcached_port == 0 || space_no != cfg.memcached_space);

		u32 arity_max = (cfg_space->cardinality > 0) ?
					cfg_space->cardinality : UINT32_MAX;

		struct space *space = space_create(space_no, 0, arity_max);

		space_init_field_defs(space, cfg_space);

		/* fill space indexes */
		@try {
			for (int j = 0; cfg_space->index[j] != NULL; ++j) {
				space_init_index(space, cfg_space->index[j]);
			}
		} @catch(tnt_Exception *e) {
			space_destroy(space);
			@throw;
		}

		say_info("space %u successfully configured", space_no);
	}
}

void
space_init(void)
{
	spaces = mh_i32ptr_new();

	/* configure regular spaces */
	space_config();
}

void
begin_build_primary_indexes(void)
{
	assert(primary_indexes_enabled == false);

	mh_int_t i;

	mh_foreach(spaces, i) {
		struct space *space = mh_i32ptr_node(spaces, i)->val;
		Index *index = space->index[0];
		[index beginBuild];
	}
}

void
end_build_primary_indexes(void)
{
	mh_int_t i;
	mh_foreach(spaces, i) {
		struct space *space = mh_i32ptr_node(spaces, i)->val;
		Index *index = space->index[0];
		[index endBuild];
	}
	primary_indexes_enabled = true;
}

void
build_secondary_indexes(void)
{
	assert(primary_indexes_enabled == true);
	assert(secondary_indexes_enabled == false);

	mh_int_t i;
	mh_foreach(spaces, i) {
		struct space *space = mh_i32ptr_node(spaces, i)->val;

		if (space->index_count <= 1)
			continue; /* no secondary keys */

		say_info("Building secondary keys in space %d...", space->no);

		Index *pk = space->index[0];
		for (int j = 1; j < space->index_count; j++) {
			Index *index = space->index[j];
			[index build: pk];
		}

		say_info("Space %d: done", space->no);
	}

	/* enable secondary indexes now */
	secondary_indexes_enabled = true;
}

i32
check_spaces(struct tarantool_cfg *conf)
{
	/* exit if no spaces are configured */
	if (conf->space == NULL) {
		return 0;
	}

	for (size_t i = 0; conf->space[i] != NULL; ++i) {
		typeof(conf->space[i]) space = conf->space[i];

		if (!CNF_STRUCT_DEFINED(space)) {
			/* space undefined, skip it */
			continue;
		}

		if (!space->enabled) {
			/* space disabled, skip it */
			continue;
		}

		if (conf->memcached_port && i == conf->memcached_space) {
			out_warning(0, "Space %i is already used as "
				    "memcached_space.", i);
			return -1;
		}

		/* at least one index in space must be defined
		 * */
		if (space->index == NULL) {
			out_warning(0, "(space = %zu) "
				    "at least one index must be defined", i);
			return -1;
		}

		int max_key_fieldno = -1;

		/* check spaces indexes */
		for (size_t j = 0; space->index[j] != NULL; ++j) {
			typeof(space->index[j]) index = space->index[j];
			u32 key_part_count = 0;
			enum index_type index_type;

			/* check index bound */
			if (j >= BOX_INDEX_MAX) {
				/* maximum index in space reached */
				out_warning(0, "(space = %zu index = %zu) "
					    "too many indexed (%i maximum)", i, j, BOX_INDEX_MAX);
				return -1;
			}

			/* at least one key in index must be defined */
			if (index->key_field == NULL) {
				out_warning(0, "(space = %zu index = %zu) "
					    "at least one field must be defined", i, j);
				return -1;
			}

			/* check unique property */
			if (index->unique == -1) {
				/* unique property undefined */
				out_warning(0, "(space = %zu index = %zu) "
					    "unique property is undefined", i, j);
			}

			for (size_t k = 0; index->key_field[k] != NULL; ++k) {
				typeof(index->key_field[k]) key = index->key_field[k];

				if (key->fieldno == -1) {
					/* last key reached */
					break;
				}

				/* key must has valid type */
				if (STR2ENUM(field_data_type, key->type) == field_data_type_MAX) {
					out_warning(0, "(space = %zu index = %zu) "
						    "unknown field data type: `%s'", i, j, key->type);
					return -1;
				}

				if (max_key_fieldno < key->fieldno) {
					max_key_fieldno = key->fieldno;
				}

				++key_part_count;
			}

			/* Check key part count. */
			if (key_part_count == 0) {
				out_warning(0, "(space = %zu index = %zu) "
					    "at least one field must be defined", i, j);
				return -1;
			}

			index_type = STR2ENUM(index_type, index->type);

			/* check index type */
			if (index_type == index_type_MAX) {
				out_warning(0, "(space = %zu index = %zu) "
					    "unknown index type '%s'", i, j, index->type);
				return -1;
			}

			/* First index must be unique. */
			if (j == 0 && index->unique == false) {
				out_warning(0, "(space = %zu) space first index must be unique", i);
				return -1;
			}
			switch (index_type) {
			case HASH:
				/* hash index must be unique */
				if (!index->unique) {
					out_warning(0, "(space = %zu index = %zu) "
					            "hash index must be unique", i, j);
					return -1;
				}
				break;
			case TREE:
				/* extra check for tree index not needed */
				break;
			default:
				assert(false);
			}
		}

		/* Check for index field type conflicts */
		if (max_key_fieldno >= 0) {
			char *types = alloca(max_key_fieldno + 1);
			memset(types, UNKNOWN, max_key_fieldno + 1);
			for (size_t j = 0; space->index[j] != NULL; ++j) {
				typeof(space->index[j]) index = space->index[j];
				for (size_t k = 0; index->key_field[k] != NULL; ++k) {
					typeof(index->key_field[k]) key = index->key_field[k];
					int f = key->fieldno;
					if (f == -1) {
						break;
					}
					enum field_data_type t = STR2ENUM(field_data_type, key->type);
					assert(t != field_data_type_MAX);
					if (types[f] != t) {
						if (types[f] == UNKNOWN) {
							types[f] = t;
						} else {
							out_warning(0, "(space = %zu fieldno = %zu) "
								    "index field type mismatch", i, f);
							return -1;
						}
					}
				}

			}
		}
	}

	return 0;
}

