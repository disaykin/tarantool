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
#include <lua/init.h>
#include <exception.h>
#include "tuple.h"
#include <pickle.h>
#include <palloc.h>
#include <assoc.h>
#include <fiber.h>
#include <tbuf.h>

#include <box/box.h>
#include "port.h"
#include "request.h"
#include "box_lua_space.h"

static struct mh_i32ptr_t *spaces_by_no;
static struct mh_lstrptr_t *spaces_by_name;

bool secondary_indexes_enabled = false;
bool primary_indexes_enabled = false;

static void
space_create_index(struct space *sp, u32 index_no, const void *name,
		   enum index_type type, bool is_unique, u32 part_count,
		   u32 *fields);
static void
space_destroy_index(struct space *sp, u32 index_no);

static struct space *
space_new(void)
{
	struct space *sp = calloc(1, sizeof(*sp));
	if (unlikely(sp == NULL)) {
		tnt_raise(LoggedError, :ER_MEMORY_ISSUE, sizeof(*sp),
			  "space", "space");
	}

	sp->no = UINT32_MAX; /* set some invalid id, space_no = 0 is valid */

	return sp;
}

static void
space_delete(struct space *sp)
{
	struct mh_i32ptr_node_t no_node = { .key = sp->no };
	mh_i32ptr_remove(spaces_by_no, &no_node, NULL, NULL);

	const void *name = sp->name;
	u32 len = load_varint32(&name);
	if (len != 0) {
		struct mh_lstrptr_node_t name_node = { .key = sp->name };
		mh_lstrptr_remove(spaces_by_name, &name_node, NULL, NULL);
	}

	for (u32 j = 0 ; j < BOX_INDEX_MAX; j++) {
		if (sp->index[j] == NULL)
			continue;

		space_destroy_index(sp, j);
	}

	free(sp->field_types);
	free(sp);
}

static void
space_create_index(struct space *sp, u32 index_no, const void *name,
		   enum index_type type, bool is_unique, u32 part_count,
		   u32 *fields)
{
	assert(part_count > 0);
	assert(index_no < BOX_INDEX_MAX);
	assert(sp->index[index_no] == NULL);
	assert(name != NULL);

	size_t sz = 0;

	sp->index[index_no] = NULL;
	struct key_def *kd = &sp->key_defs[index_no];
	memset(kd, 0, sizeof(*kd));

	kd->type = type;
	kd->is_unique = is_unique;

	kd->part_count = part_count;
	sz = sizeof(*kd->parts) * kd->part_count;
	kd->parts = malloc(sz);
	if (kd->parts == NULL)
		goto error_1;

	kd->max_fieldno = 0;
	for (u32 part = 0; part < part_count; part++) {
		kd->max_fieldno = MAX(kd->max_fieldno, fields[part] + 1);
	}

	sz = kd->max_fieldno * sizeof(u32);
	kd->cmp_order = malloc(sz);
	if (kd->cmp_order == NULL)
		goto error_2;

	for (u32 field_no = 0; field_no < kd->max_fieldno; field_no++) {
		kd->cmp_order[field_no] = BOX_FIELD_MAX;
	}

	for (u32 part = 0; part < kd->part_count; part++) {
		kd->parts[part].fieldno = fields[part];
		assert(kd->parts[part].fieldno < kd->max_fieldno);
		kd->parts[part].type = sp->field_types[fields[part]];
		assert(kd->parts[part].type != UNKNOWN);
		kd->cmp_order[kd->parts[part].fieldno] = part;
	}

	sz = sizeof(Index *);
	sp->index[index_no] = [[Index alloc :kd->type :kd :sp] init :kd :sp];
	if (sp->index[index_no] == NULL)
		goto error_3;

	sp->index[index_no]->no = index_no;
	u32 name_len = load_varint32(&name);
	save_field(sp->index[index_no]->name, name, name_len);

	return;

error_3:
	free(kd->cmp_order);
error_2:
	free(kd->parts);
error_1:
	tnt_raise(LoggedError, :ER_MEMORY_ISSUE, sz,
		  "space", "index");
}

static void
space_destroy_index(struct space *sp, u32 index_no)
{
	assert(index_no < BOX_INDEX_MAX);
	assert(sp->index[index_no] != NULL);
	struct key_def *kd = &sp->key_defs[index_no];
	Index *index = sp->index[index_no];

	free(kd->parts);
	free(kd->cmp_order);
	memset(kd, 0, sizeof(*kd));

	[index free];
	sp->index[index_no] = NULL;
}

static void
space_create_sysspace_space(void)
{
	struct space *sp = space_new();
	@try {
		sp->no = BOX_SYSSPACE_SPACE_NO;
		save_field(sp->name, BOX_SYSSPACE_SPACE_NAME,
			   strlen(BOX_SYSSPACE_SPACE_NAME));

		sp->flags = SPACE_FLAG_TEMPORARY;
		sp->max_fieldno = 4;
		size_t sz = sp->max_fieldno * sizeof(*sp->field_types);
		sp->field_types = malloc(sz);
		if (sp->field_types == NULL) {
			tnt_raise(LoggedError, :ER_MEMORY_ISSUE ,sz,
				  "space", "types");
		}

		sp->field_types[0] = NUM;
		sp->field_types[1] = STRING;
		sp->field_types[2] = NUM;
		sp->field_types[3] = NUM;

		char name[16];

		/* space_no: TREE, unique=1, {space_no} - space_no uniqueness */
		save_field(name, "pk", strlen("pk"));
		space_create_index(sp, 0, name, TREE, true, 1, (u32[]){ 0 });

		/* name: TREE, unique=1, {name} - name uniqueness */
		save_field(name, "name", strlen("name"));
		space_create_index(sp, 1, name, TREE, true, 1, (u32[]){ 1 });

		/* Put space into the cache */
		mh_int_t pos;
		struct mh_i32ptr_node_t no_node = { .key = sp->no, .val = sp };
		pos = mh_i32ptr_replace(spaces_by_no, &no_node, NULL,
					NULL, NULL);
		if (pos == mh_end(spaces_by_no)) {
			tnt_raise(LoggedError, :ER_MEMORY_ISSUE,
				  sizeof(no_node), "spaces_by_no", "space");
		}

		struct mh_lstrptr_node_t name_node = { .key = sp->name,
						       .val = sp };
		pos = mh_lstrptr_replace(spaces_by_name, &name_node, NULL,
					 NULL, NULL);
		if (pos == mh_end(spaces_by_name)) {
			mh_i32ptr_remove(spaces_by_no, &no_node, NULL, NULL);
			tnt_raise(LoggedError, :ER_MEMORY_ISSUE,
				  sizeof(name_node), "spaces_by_name", "space");
		}
	} @catch(tnt_Exception *e) {
		space_delete(sp);
		@throw;
	}

	sp->is_valid = true;
	say_info("system space '%s' successfully configured",
		 BOX_SYSSPACE_SPACE_NAME);
}

static void
space_create_sysspace_index(void)
{
	struct space *sp = space_new();
	@try {
		sp->no = BOX_SYSSPACE_INDEX_NO;
		save_field(sp->name, BOX_SYSSPACE_INDEX_NAME,
			   strlen(BOX_SYSSPACE_INDEX_NAME));

		sp->flags = SPACE_FLAG_TEMPORARY;
		sp->max_fieldno = 5;
		size_t sz = sp->max_fieldno * sizeof(*sp->field_types);
		sp->field_types = malloc(sz);
		if (sp->field_types == NULL) {
			tnt_raise(LoggedError, :ER_MEMORY_ISSUE ,sz,
				  "space", "types");
		}

		sp->field_types[0] = NUM;	/* index_no */
		sp->field_types[1] = STRING;	/* name */
		sp->field_types[2] = NUM;	/* space_no */
		sp->field_types[3] = NUM;	/* type */
		sp->field_types[4] = NUM;	/* is_unique */

		char name[16];

		/* pk: TREE, unique=1, {space_no, index_no} - no uniqueness*/
		save_field(name, "pk", strlen("pk"));
		space_create_index(sp, 0, name, TREE, true, 2, (u32[]){ 2, 0 });

		/* name: TREE, unique=1, {space_no, name} - name uniqueness*/
		save_field(name, "name", strlen("name"));
		space_create_index(sp, 1, name, TREE, true, 2, (u32[]){ 2, 1 });

		/* Put space into the cache */
		mh_int_t pos;
		struct mh_i32ptr_node_t no_node = { .key = sp->no, .val = sp };
		pos = mh_i32ptr_replace(spaces_by_no, &no_node, NULL,
					NULL, NULL);
		if (pos == mh_end(spaces_by_no)) {
			tnt_raise(LoggedError, :ER_MEMORY_ISSUE,
				  sizeof(no_node), "spaces_by_no", "space");
		}

		struct mh_lstrptr_node_t name_node = { .key = sp->name,
						       .val = sp };
		pos = mh_lstrptr_replace(spaces_by_name, &name_node, NULL,
					 NULL, NULL);
		if (pos == mh_end(spaces_by_name)) {
			mh_i32ptr_remove(spaces_by_no, &no_node, NULL, NULL);
			tnt_raise(LoggedError, :ER_MEMORY_ISSUE,
				  sizeof(name_node), "spaces_by_name", "space");
		}
	} @catch(tnt_Exception *e) {
		space_delete(sp);
		@throw;
	}

	sp->is_valid = true;
	say_info("system space '%s' successfully configured",
		 BOX_SYSSPACE_INDEX_NAME);
}

static const char *
format_name_or_no(const void *name, u32 no)
{
	enum { NAME_BUF_SIZE = BOX_SPACE_NAME_MAXLEN + 14 };
	static char name_buf[NAME_BUF_SIZE];

	if (name != NULL) {
		u32 name_len = load_varint32(&name);
		assert (name_len < BOX_SPACE_NAME_MAXLEN);
		snprintf(name_buf, NAME_BUF_SIZE, "'%.*s'",
			 name_len, (char *) name);
	} else {
		snprintf(name_buf, NAME_BUF_SIZE, "%u", no);
	}

	name_buf[NAME_BUF_SIZE - 1] = 0;

	return name_buf;
}

#define space_meta_raise(sp, fmt, ...) ({				\
	enum {	MSG_BUF_SIZE = 1024 };					\
									\
	char msg_buf[MSG_BUF_SIZE];					\
	snprintf(msg_buf, MSG_BUF_SIZE-1, fmt, ##__VA_ARGS__);		\
	msg_buf[MSG_BUF_SIZE-1] = 0;					\
									\
	tnt_raise(LoggedError, :ER_SPACE_META,				\
		  format_name_or_no(sp->name, sp->no), msg_buf);	\
})

static void
space_cache_update_do_index(struct space *space_cur,
			    struct tuple *index_meta_new)
{
	const void *d = index_meta_new->data;
	bool is_empty = (space_cur->index[0] == NULL) ||
			space_size(space_cur) == 0;

	/*
	 * index_no
	 */
	u32 index_no;
	u32 size = load_varint32(&d);
	assert(size == sizeof(index_no));
	index_no = *(u32 *) d;
	d += size;
	assert (index_no < BOX_INDEX_MAX);

	/*
	 * name
	 */
	u32 name_len = load_varint32(&d);
	const void *name = d;
	d += name_len;

	/*
	 * space_no
	 */
	u32 space_no;
	size = load_varint32(&d);
	assert(size == sizeof(space_no));
	space_no = *(u32 *) d;
	d+= size;
	assert (space_no == space_cur->no);

	/*
	 * type
	 */
	u32 type;
	size = load_varint32(&d);
	assert(size == sizeof(type));
	type = *(u32 *) d;
	d+= size;

	/*
	 * is_unique
	 */
	u32 is_unique_buf;
	size = load_varint32(&d);
	assert(size == sizeof(is_unique_buf));
	is_unique_buf = *(u32 *) d;
	bool is_unique = (is_unique_buf != 0);
	d+= size;

	/* size of variable part of meta_cur tuple */
	u32 part_count = (index_meta_new->field_count - 5);

	/* Calculate max_fieldno */
	u32 max_fieldno = 0;
	u32 *fields = palloc(fiber->gc_pool, part_count * sizeof(*fields));
	for (u32 part = 0; part < part_count; part++) {
		/* fieldno */
		size = load_varint32(&d);
		assert(size == sizeof(fields[part]));
		memcpy(&fields[part], d, size);
		d += sizeof(fields[part]);
		max_fieldno = MAX(max_fieldno, fields[part] + 1);

		if (space_cur->max_fieldno > space_cur->max_fieldno ||
		    space_cur->field_types[fields[part]] == UNKNOWN) {
			space_meta_raise(space_cur,
				"Index %u: type is not defined for field %u",
				index_no, fields[part]);
		}
	}

	assert (d == index_meta_new->data + index_meta_new->bsize);
	/* Update max_fieldno in the space */
	space_cur->max_fieldno = MAX(space_cur->max_fieldno, max_fieldno);

	/* Check if key_def was changed */
	struct key_def *key_def = &space_cur->key_defs[index_no];
	bool key_def_changed = false;
	if (space_cur->index[index_no] == NULL) {
		key_def_changed = true;
	} else if (key_def->part_count != part_count ||
		   key_def->is_unique != is_unique ||
		   key_def->type != type) {
		key_def_changed = true;
	} else {
		for (u32 part = 0; part < part_count; part++) {
			if (key_def->parts[part].fieldno != fields[part] ||
			    key_def->parts[part].type !=
					space_cur->field_types[fields[part]]) {
				key_def_changed = true;
				break;
			}
		}
	}

	if (key_def_changed) {
		if (!is_empty) {
			space_meta_raise(space_cur, "Index %u: "
					 "key definition is read-only because"
					 "space is not empty",
					 index_no);
		}

		/* Drop the old index */
		if (space_cur->index[index_no] != NULL) {
			space_destroy_index(space_cur, index_no);
		}

		/* Create a new one */
		space_create_index(space_cur, index_no, name, type, is_unique,
				   part_count, fields);
	} else {
		/* Update the other param which do not affect key_def */
		Index *index = space_cur->index[index_no];
		assert (index != NULL);

		save_field(index->name, name, name_len);
	}
}

static void
space_cache_update_do_space(struct space *space_cur,
			    struct tuple *space_meta_new)
{
	const void *d = space_meta_new->data;
	bool is_empty = (space_cur->index[0] == NULL) ||
			space_size(space_cur) == 0;

	/*
	 * space_no (read-only)
	 */
	u32 space_no = 0;
	u32 size = load_varint32(&d);
	assert(size == sizeof(space_no));
	space_no = *(u32 *) d;
	(void) space_no;
	/* space_no currently can not be changed */
	assert (space_no == space_cur->no);
	d+= size;

	/*
	 * name (read-write)
	 */
	size = load_varint32(&d);
	save_field(space_cur->name, d, size);
	d += size;

	/*
	 * arity (is read-only if space is non-empty)
	 */
	size = load_varint32(&d);
	u32 arity;
	memcpy(&arity, d, size);
	d += sizeof(space_cur->arity);
	if (!is_empty && space_cur->arity != arity) {
		space_meta_raise(space_cur, "'arity' is read-only because"
				 "space is not empty");
	}
	space_cur->arity = arity;

	/*
	 * flags
	 */
	u32 flags = 0;
	size = load_varint32(&d);
	memcpy(&flags, d, size);
	d += sizeof(flags);
	if ((space_cur->flags & SPACE_FLAG_TEMPORARY) &&
	    !(flags & SPACE_FLAG_TEMPORARY)) {
		space_meta_raise(space_cur,
				 "SPACE_FLAG_TEMPORARY is read-only");
	}

	/*
	 * Field types
	 */

	/* size of variable part of meta_cur tuple / 2 */
	u32 field_def_count = (space_meta_new->field_count - 4) / 2;

	/* Calculate max_fieldno */
	const void *d_svp = d;
	u32 max_fieldno = 0;
	for (u32 i = 0; i < field_def_count; i++) {
		/* field no */
		u32 field_no;
		size = load_varint32(&d);
		assert(size == sizeof(field_no));
		memcpy(&field_no, d, size);
		d += sizeof(field_no);

		/* field type */
		u32 field_type;
		size = load_varint32(&d);
		assert(size == sizeof(field_type));
		memcpy(&field_type, d, size);
		d += sizeof(field_type);

		max_fieldno = MAX(max_fieldno, field_no + 1);
		if (is_empty) {
			continue;
		}

		if (max_fieldno > space_cur->max_fieldno ||
		    space_cur->field_types[field_no] != field_type) {
			space_meta_raise(space_cur,
					 "field defintions are read-only "
					 "because space is not empty");
		}
	}
	d = d_svp;

	/* Allocate field_types */
	free(space_cur->field_types);
	space_cur->field_types = NULL;
	size_t sz = max_fieldno * sizeof(space_cur->field_types);
	space_cur->field_types = malloc(sz);
	if (space_cur->field_types == NULL) {
		tnt_raise(LoggedError, :ER_MEMORY_ISSUE, sz,
			  "space", "field types");
	}
	memset(space_cur->field_types, 0, sizeof(sz));

	/* Update field types */
	for (u32 i = 0; i < field_def_count; i++) {
		/* fieldno */
		u32 field_no;
		size = load_varint32(&d);
		assert(size == sizeof(field_no));
		memcpy(&field_no, d, size);
		d += sizeof(field_no);

		u32 field_type;
		size = load_varint32(&d);
		assert(size == sizeof(field_type));
		memcpy(&field_type, d, size);
		d += sizeof(field_type);

		space_cur->field_types[field_no] = field_type;
	}

	assert (d == space_meta_new->data + space_meta_new->bsize);
}

static struct space *
space_cache_update(struct tuple *space_meta_new)
{
	/*
	 * Try to get a previous version of the space cache
	 */
	struct space *space_cur = NULL;

	const void *d = space_meta_new->data;
	u32 space_no = 0;
	u32 size = load_varint32(&d);
	assert(size == sizeof(space_no));
	space_no = *(u32 *) d;

	say_info("Space %u: updating configuration...", space_no);

	struct mh_i32ptr_node_t no_node = { .key = space_no };
	mh_int_t k = mh_i32ptr_get(spaces_by_no, &no_node, NULL, NULL);
	if (k != mh_end(spaces_by_no)) {
		/*
		 * A previous version of the space cache exists.
		 *
		 * Remove the entry from spaces_by_name hashtable, but leave it
		 * in spaces_by_no. Space name can be changed during the update
		 * procedure, but space_no is permanent.
		 */

		space_cur = mh_i32ptr_node(spaces_by_no, k)->val;
		struct mh_lstrptr_node_t name_node = { .key = space_cur->name };
		mh_lstrptr_remove(spaces_by_name, &name_node, NULL, NULL);
	} else {
		/*
		 * A previous version of the space cache does not exists.
		 *
		 * Create a new entry and save it only in space_by_no.
		 */
		space_cur = space_new();
		space_cur->no = space_no;
		no_node.val = space_cur;

		mh_int_t pos;
		pos = mh_i32ptr_replace(spaces_by_no, &no_node, NULL, NULL, NULL);
		if (pos == mh_end(spaces_by_no)) {
			space_delete(space_cur);
			tnt_raise(LoggedError, :ER_MEMORY_ISSUE,
				  sizeof(no_node), "spaces_by_no", "space");
		}
	}

	/*
	 * At this point the cache entry exists only in space_by_no hashtable.
	 * Mark this entry as expired (the update procedure can fail)
	 */
	space_cur->is_valid = false;

	/* Get the meta space */
	struct space *sysspace_index = space_find_by_no(BOX_SYSSPACE_INDEX_NO);

	/* Update space itself */
	space_cache_update_do_space(space_cur, space_meta_new);

	/* Update all indexes */
	void *space_key = palloc(fiber->gc_pool,
				 varint32_sizeof(space_cur->no) +
				 sizeof(space_cur->no));
	save_field(space_key, &space_cur->no, sizeof(space_cur->no));
	Index *index = index_find_by_no(sysspace_index, 0);
	struct iterator *it = [index allocIterator];
	@try {
		[index initIterator: it :ITER_EQ :space_key :1];

		struct tuple *index_meta = NULL;
		while ((index_meta = it->next(it))) {
			space_cache_update_do_index(space_cur, index_meta);
		}
	} @finally {
		it->free(it);
	}

	/*
	 * Perform post checks
	 */

	/* Check if pk is configured */
	if (space_cur->index[0] == NULL) {
		space_meta_raise(space_cur, "primary key is not configured");
	}

	/* Check if pk is unique */
	if (!space_cur->key_defs[0].is_unique) {
		space_meta_raise(space_cur, "primary key must be unique");
	}

	/* The entry is ok, put it back to spaces_by_name cache */
	struct mh_lstrptr_node_t name_node = { .key = space_cur->name };
	mh_int_t pos = mh_lstrptr_replace(spaces_by_name, &name_node, NULL,
					 NULL, NULL);
	if (pos == mh_end(spaces_by_name)) {
		tnt_raise(LoggedError, :ER_MEMORY_ISSUE,
			  sizeof(no_node), "spaces_by_name", "space");
	}

	/* Cache entry is valid and exists in both hash tables */
	space_cur->is_valid = true;

	say_info("Space %u: done", space_no);

	return space_cur;
}

static struct space *
space_cache_miss_no(u32 space_no)
{
	/*
	 * Try to get metadata by space no
	 */
	struct tuple *space_meta_new = NULL;

	struct space *sysspace_space = space_find_by_no(BOX_SYSSPACE_SPACE_NO);

	void *space_key = palloc(fiber->gc_pool,
		varint32_sizeof(space_no) + sizeof(space_no));
	save_field(space_key, &space_no, sizeof(space_no));
	Index *index = index_find_by_no(sysspace_space, 0);
	struct iterator *it = [index allocIterator];
	@try {
		[index initIterator: it :ITER_EQ :space_key :1];
		space_meta_new = it->next(it);
	} @finally {
		it->free(it);
	}

	if (space_meta_new == NULL) {
		tnt_raise(ClientError, :ER_NO_SUCH_SPACE,
			  format_name_or_no(NULL, space_no));
	}

	return space_cache_update(space_meta_new);
}

static struct space *
space_cache_miss_name(const void *name)
{
	assert (name != NULL);

	/*
	 * Try to get metadata by space name
	 */
	struct tuple *space_meta_new = NULL;

	struct space *sysspace_space = space_find_by_no(BOX_SYSSPACE_SPACE_NO);

	/* Try to lookup the space metadata by space name */
	void *space_key = (void *) name;
	Index *index = index_find_by_no(sysspace_space, 1);
	struct iterator *it = [index allocIterator];
	@try {
		[index initIterator: it :ITER_EQ :space_key :1];
		space_meta_new = it->next(it);
	} @finally {
		it->free(it);
	}

	if (space_meta_new == NULL) {
		tnt_raise(ClientError, :ER_NO_SUCH_SPACE,
			  format_name_or_no(name, 0));
	}

	return space_cache_update(space_meta_new);
}

/* return space by its number */
struct space *
space_find_by_no(u32 space_no)
{
	const struct mh_i32ptr_node_t node = { .key = space_no };
	mh_int_t k = mh_i32ptr_get(spaces_by_no, &node, NULL, NULL);
	if (likely(k != mh_end(spaces_by_no))) {
		struct space *space_cur = mh_i32ptr_node(spaces_by_no, k)->val;
		if (likely(space_cur->is_valid))
			return space_cur;
	}

	return space_cache_miss_no(space_no);
}

struct space *
space_find_by_name(const void *name)
{
	struct mh_lstrptr_node_t node = { .key = name };
	mh_int_t k = mh_lstrptr_get(spaces_by_name, &node, NULL, NULL);
	if (likely(k != mh_end(spaces_by_name))) {
		struct space *space_cur = mh_lstrptr_node(spaces_by_name, k)->val;
		if (likely(space_cur->is_valid))
			return space_cur;
	}

	return space_cache_miss_name(name);
}

Index *
index_find_by_no(struct space *sp, u32 index_no)
{
	if (index_no >= BOX_INDEX_MAX || sp->index[index_no] == NULL)
		tnt_raise(LoggedError, :ER_NO_SUCH_INDEX, index_no,
			  space_n(sp));
	return sp->index[index_no];
}

/**
 * Visit all enabled spaces and apply 'func'.
 */
void
space_foreach(void (*func)(struct space *sp, void *udata), void *udata) {

	mh_int_t i;
	mh_foreach(spaces_by_no, i) {
		struct space *space = mh_i32ptr_node(spaces_by_no, i)->val;
		if (!space->is_valid)
			continue;
		func(space, udata);
	}
}

size_t
space_size(struct space *sp)
{
	return [index_find_by_no(sp, 0) size];
}

struct tuple *
space_replace(struct space *sp, struct tuple *old_tuple,
	      struct tuple *new_tuple, enum dup_replace_mode mode)
{
	u32 i = 0;
	@try {
		/* Update the primary key */
		Index *pk = index_find_by_no(sp, 0);
		assert(pk->key_def->is_unique);
		/*
		 * If old_tuple is not NULL, the index
		 * has to find and delete it, or raise an
		 * error.
		 */
		old_tuple = [pk replace: old_tuple :new_tuple :mode];

		assert(old_tuple || new_tuple);

		if (!secondary_indexes_enabled)
			return old_tuple;

		/* Update secondary keys */
		for (i = i + 1; i < BOX_INDEX_MAX; i++) {
			if (sp->index[i] == NULL)
				continue;
			Index *index = sp->index[i];
			[index replace: old_tuple :new_tuple :DUP_INSERT];
		}
		return old_tuple;
	} @catch (tnt_Exception *e) {
		/* Rollback all changes */
		for (; i > 0; i--) {
			Index *index = sp->index[i-1];
			[index replace: new_tuple: old_tuple: DUP_INSERT];
		}
		@throw;
	}
}

void
space_validate_tuple(struct space *sp, struct tuple *new_tuple)
{
	/* Check to see if the tuple has a sufficient number of fields. */
	if (new_tuple->field_count < sp->max_fieldno)
		tnt_raise(IllegalParams,
			  :"tuple must have all indexed fields");

	if (sp->arity > 0 && sp->arity != new_tuple->field_count)
		tnt_raise(IllegalParams,
			  :"tuple field count must match space cardinality");

	/* Sweep through the tuple and check the field sizes. */
	const u8 *data = new_tuple->data;
	for (u32 f = 0; f < sp->max_fieldno; ++f) {
		/* Get the size of the current field and advance. */
		u32 len = load_varint32((const void **) &data);
		data += len;
		/*
		 * Check fixed size fields (NUM and NUM64) and
		 * skip undefined size fields (STRING and UNKNOWN).
		 */
		if (sp->field_types[f] == NUM) {
			if (len != sizeof(u32))
				tnt_raise(ClientError, :ER_KEY_FIELD_TYPE,
					  "u32");
		} else if (sp->field_types[f] == NUM64) {
			if (len != sizeof(u64))
				tnt_raise(ClientError, :ER_KEY_FIELD_TYPE,
					  "u64");
		}
	}
}

void
space_free(void)
{
	mh_int_t i;
	mh_foreach(spaces_by_no, i) {
		struct space *space = mh_i32ptr_node(spaces_by_no, i)->val;
		space_delete(space);
	}
}

/**
 * @brief Create a new meta tuple based on confetti space configuration
 */
static struct tuple *
space_config_convert_space(tarantool_cfg_space *cfg_space, u32 space_no)
{
	u32 max_fieldno = 0;
	for (u32 i = 0; cfg_space->index[i] != NULL; ++i) {
		typeof(cfg_space->index[i]) cfg_index = cfg_space->index[i];

		/* Calculate key part count and maximal field number. */
		for (u32 part = 0; cfg_index->key_field[part] != NULL; ++part) {
			typeof(cfg_index->key_field[part]) cfg_key =
					cfg_index->key_field[part];

			if (cfg_key->fieldno == -1) {
				/* last filled key reached */
				break;
			}

			max_fieldno = MAX(max_fieldno, cfg_key->fieldno + 1);
		}
	}

	assert(max_fieldno > 0);

	enum field_data_type *field_types =
			palloc(fiber->gc_pool, max_fieldno * sizeof(u32));
	memset(field_types, 0, max_fieldno * sizeof(u32));

	u32 defined_fieldno = 0;
	for (u32 i = 0; cfg_space->index[i] != NULL; ++i) {
		typeof(cfg_space->index[i]) cfg_index = cfg_space->index[i];

		/* Calculate key part count and maximal field number. */
		for (u32 part = 0; cfg_index->key_field[part] != NULL; ++part) {
			typeof(cfg_index->key_field[part]) cfg_key =
					cfg_index->key_field[part];

			if (cfg_key->fieldno == -1) {
				/* last filled key reached */
				break;
			}

			enum field_data_type t =  STR2ENUM(field_data_type,
							   cfg_key->type);
			if (field_types[cfg_key->fieldno] == t)
				continue;

			assert (field_types[cfg_key->fieldno] == UNKNOWN);
			field_types[cfg_key->fieldno] = t;
			defined_fieldno++;
		}
	}

	char name_buf[11];
	sprintf(name_buf, "%u", space_no);
	size_t name_len = strlen(name_buf);

	size_t bsize = varint32_sizeof(name_len) + name_len +
		       (varint32_sizeof(sizeof(u32)) + sizeof(u32)) *
		       (3 + 2 * defined_fieldno);

	struct tuple *tuple = tuple_alloc(bsize);
	assert (tuple != NULL);
	tuple->field_count = 1 + 3 + 2 * defined_fieldno;

	void *d = tuple->data;
	/* space_no */
	d = save_field(d, &space_no, sizeof(space_no));

	/* name */
	d = save_field(d, name_buf, name_len);

	/* arity */
	u32 arity = (cfg_space->cardinality != -1) ? cfg_space->cardinality : 0;
	d = save_field(d, &arity, sizeof(arity));

	u32 flags = 0;
	d = save_field(d, &flags, sizeof(flags));

	for (u32 fieldno = 0; fieldno < max_fieldno; fieldno++) {
		u32 type = field_types[fieldno];
		if (type == UNKNOWN)
			continue;

		d = save_field(d, &fieldno, sizeof(fieldno));
		d = save_field(d, &type, sizeof(type));
		defined_fieldno--;
	}

	assert (defined_fieldno == 0);
	assert (tuple->data + tuple->bsize == d);

#if defined(DEBUG)
	struct tbuf *out = tbuf_new(fiber->gc_pool);
	tuple_print(out, tuple->field_count, tuple->data);
	say_debug("Space %u meta: %.*s",
		  space_no, (int) out->size, tbuf_str(out));
#endif /* defined(DEBUG) */

	return tuple;
}

/**
 * @brief Create a new meta tuple based on confetti index configuration
 */
static struct tuple *
space_config_convert_index(tarantool_cfg_space_index *cfg_index,
			   u32 space_no, u32 index_no)
{
	u32 defined_fieldno = 0;
	/* Calculate key part count and maximal field number. */
	for (u32 part = 0; cfg_index->key_field[part] != NULL; ++part) {
		typeof(cfg_index->key_field[part]) cfg_key =
				cfg_index->key_field[part];

		if (cfg_key->fieldno == -1) {
			/* last filled key reached */
			break;
		}

		defined_fieldno++;
	}

	assert(defined_fieldno > 0);

	char name_buf[11];
	if (index_no != 0) {
		sprintf(name_buf, "%u", index_no);
	} else {
		strcpy(name_buf, "pk");
	}
	size_t name_len = strlen(name_buf);

	size_t bsize = varint32_sizeof(name_len) + name_len +
		       (varint32_sizeof(sizeof(u32)) + sizeof(u32)) *
		       (4 + defined_fieldno);

	struct tuple *tuple = tuple_alloc(bsize);
	assert (tuple != NULL);
	tuple->field_count = 1 + 4 + defined_fieldno;

	void *d = tuple->data;
	/* index_no */
	d = save_field(d, &index_no, sizeof(index_no));

	/* name */
	d = save_field(d, name_buf, name_len);

	/* space_no */
	d = save_field(d, &space_no, sizeof(space_no));

	/* type */
	u32 type = STR2ENUM(index_type, cfg_index->type);
	assert (type < index_type_MAX);
	d = save_field(d, &type, sizeof(type));

	/* unique */
	u32 unique = (cfg_index->unique) ? 1 : 0;
	d = save_field(d, &unique, sizeof(unique));

	for (u32 part = 0; cfg_index->key_field[part] != NULL; ++part) {
		typeof(cfg_index->key_field[part]) cfg_key =
				cfg_index->key_field[part];

		if (cfg_key->fieldno == -1) {
			/* last filled key reached */
			break;
		}

		u32 fieldno = cfg_key->fieldno;
		assert (fieldno < BOX_FIELD_MAX);
		d = save_field(d, &fieldno, sizeof(fieldno));

		defined_fieldno--;
	}

	assert (defined_fieldno == 0);
	assert (tuple->data + tuple->bsize == d);

#if defined(DEBUG)
	struct tbuf *out = tbuf_new(fiber->gc_pool);
	tuple_print(out, tuple->field_count, tuple->data);
	say_debug("Space %u index %u meta: %.*s",
		  space_no, index_no, (int) out->size, tbuf_str(out));
#endif /* defined(DEBUG) */

	return tuple;
}

static struct tuple *
space_config_convert_space_memcached(u32 memcached_space)
{
	const char *name = "memcached";
	u32 name_len = strlen(name);

	u32 defined_fieldno = 1;
	size_t bsize = varint32_sizeof(name_len) + name_len +
		       (varint32_sizeof(sizeof(u32)) + sizeof(u32)) *
		       (4 + defined_fieldno);

	struct tuple *tuple = tuple_alloc(bsize);
	assert (tuple != NULL);
	tuple->field_count = 1 + 4 + defined_fieldno;

	void *d = tuple->data;
	/* space_no */
	d = save_field(d, &memcached_space, sizeof(memcached_space));

	/* name */
	d = save_field(d, name, name_len);

	/* arity */
	u32 arity = 4;
	d = save_field(d, &arity, sizeof(arity));

	/* flags */
	u32 flags = 0;
	d = save_field(d, &flags, sizeof(flags));

	u32 field_no = 0;
	u32 field_type = STRING;
	d = save_field(d, &field_no, sizeof(field_no));
	d = save_field(d, &field_type, sizeof(field_type));

	assert (tuple->data + tuple->bsize == d);
#if defined(DEBUG)
	struct tbuf *out = tbuf_new(fiber->gc_pool);
	tuple_print(out, tuple->field_count, tuple->data);
	say_debug("Space %u meta: %.*s",
		  memcached_space, (int) out->size, tbuf_str(out));
#endif /* defined(DEBUG) */

	return tuple;
}


static struct tuple *
space_config_convert_index_memcached(u32 memcached_space)
{
	static const char *name = "pk";

	u32 name_len = strlen(name);

	u32 defined_fieldno = 1;
	size_t bsize = varint32_sizeof(name_len) + name_len +
		       (varint32_sizeof(sizeof(u32)) + sizeof(u32)) *
		       (4 + defined_fieldno);

	struct tuple *tuple = tuple_alloc(bsize);
	assert (tuple != NULL);
	tuple->field_count = 1 + 4 + defined_fieldno;

	void *d = tuple->data;
	/* index_no */
	u32 index_no = 0;
	d = save_field(d, &index_no, sizeof(index_no));

	/* name */
	d = save_field(d, name, name_len);

	/* space_no */
	d = save_field(d, &memcached_space, sizeof(memcached_space));

	/* type */
	u32 type = HASH;
	d = save_field(d, &type, sizeof(type));

	/* is_unique */
	u32 is_unique = 1;
	d = save_field(d, &is_unique, sizeof(is_unique));

	u32 field_no = 0;
	d = save_field(d, &field_no, sizeof(field_no));

	assert (tuple->data + tuple->bsize == d);
#if defined(DEBUG)
	struct tbuf *out = tbuf_new(fiber->gc_pool);
	tuple_print(out, tuple->field_count, tuple->data);
	say_debug("Space %u index %u meta: %.*s",
		  memcached_space, 0, (int) out->size, tbuf_str(out));
#endif /* defined(DEBUG) */

	return tuple;
}

static void
space_config_convert(void)
{
	struct space *sysspace_space = space_find_by_no(BOX_SYSSPACE_SPACE_NO);
	struct space *sysspace_index = space_find_by_no(BOX_SYSSPACE_INDEX_NO);

	struct tuple *meta = NULL;
	Index *sysspace_space_pk = index_find_by_no(sysspace_space, 0);
	Index *sysspace_index_pk = index_find_by_no(sysspace_index, 0);

	[sysspace_space_pk beginBuild];
	[sysspace_index_pk beginBuild];
	@try {
		/* exit if no spaces are configured */
		if (cfg.space == NULL) {
			return;
		}

		/* fill box spaces */
		for (u32 i = 0; cfg.space[i] != NULL; ++i) {
			tarantool_cfg_space *cfg_space = cfg.space[i];

			if (!CNF_STRUCT_DEFINED(cfg_space) || !cfg_space->enabled)
				continue;

			assert(cfg.memcached_port == 0 || i != cfg.memcached_space);
			meta = space_config_convert_space(cfg_space, i);
			tuple_ref(meta, 1);
			[sysspace_space_pk buildNext :meta];
			meta = NULL;

			for (u32 j = 0; cfg_space->index[j] != NULL; ++j) {
				meta = space_config_convert_index(
						cfg_space->index[j], i, j);

				tuple_ref(meta, 1);
				[sysspace_index_pk buildNext :meta];
				meta = NULL;
			}
		}

		if (cfg.memcached_port != 0) {
			meta = space_config_convert_space_memcached(
						cfg.memcached_space);
			[sysspace_space_pk buildNext :meta];
			meta = NULL;

			meta = space_config_convert_index_memcached(
						cfg.memcached_space);
			[sysspace_index_pk buildNext :meta];
			meta = NULL;
		}
	} @catch(tnt_Exception *e) {
		if (meta != NULL)  {
			tuple_free(meta);
		}

		@throw;
	} @finally {
		[sysspace_space_pk endBuild];
		[sysspace_index_pk endBuild];
	}

	/* Init config spaces */
	for (u32 i = 0; cfg.space[i] != NULL; ++i) {
		if (!CNF_STRUCT_DEFINED(cfg.space[i]) || !cfg.space[i]->enabled)
			continue;

		space_find_by_no(i);
	}
}

void
space_init(void)
{
	spaces_by_no = mh_i32ptr_new();
	spaces_by_name = mh_lstrptr_new();

	/* configure system spaces */
	space_create_sysspace_space();
	space_create_sysspace_index();

	/* cconvert configuration */
	space_config_convert();
}

void
begin_build_primary_indexes(void)
{
	assert(primary_indexes_enabled == false);

	mh_int_t i;


	mh_foreach(spaces_by_no, i) {
		struct space *space = mh_i32ptr_node(spaces_by_no, i)->val;
		if (space->no == BOX_SYSSPACE_SPACE_NO ||
		    space->no == BOX_SYSSPACE_INDEX_NO)
			continue;

		say_info("Building primary keys in space %u...", space->no);
		assert (space->is_valid);

		Index *index = index_find_by_no(space, 0);
		[index beginBuild];
	}
}

void
end_build_primary_indexes(void)
{
	mh_int_t i;
	mh_foreach(spaces_by_no, i) {
		struct space *space = mh_i32ptr_node(spaces_by_no, i)->val;
		if (space->no == BOX_SYSSPACE_SPACE_NO ||
		    space->no == BOX_SYSSPACE_INDEX_NO)
			continue;

		say_info("Space %u: done", space->no);
		assert (space->is_valid);

		Index *index = index_find_by_no(space, 0);
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
	mh_foreach(spaces_by_no, i) {
		struct space *space = mh_i32ptr_node(spaces_by_no, i)->val;

		say_info("Building secondary keys in space %u...", space->no);
		assert (space->is_valid);

		Index *pk = index_find_by_no(space, 0);
		for (u32 j = 1; j < BOX_INDEX_MAX; j++) {
			if (space->index[j] == NULL)
				continue;

			Index *index = index_find_by_no(space, j);
			[index build: pk];
		}

		say_info("Space %d: done", space->no);
	}

	/* enable secondary indexes now */
	secondary_indexes_enabled = true;
}

int
check_spaces(struct tarantool_cfg *conf)
{
	/* exit if no spaces are configured */
	if (conf->space == NULL) {
		return 0;
	}

	for (size_t i = 0; conf->space[i] != NULL; ++i) {
		typeof(conf->space[i]) space = conf->space[i];

		if (i >= BOX_SPACE_MAX) {
			out_warning(0, "(space = %zu) invalid id, (maximum=%u)",
				    i, BOX_SPACE_MAX);
			return -1;
		}

		if (!CNF_STRUCT_DEFINED(space)) {
			/* space undefined, skip it */
			continue;
		}

		if (!space->enabled) {
			/* space disabled, skip it */
			continue;
		}

		if (conf->memcached_port && i == conf->memcached_space) {
			out_warning(0, "Space %zu is already used as "
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

		u32 max_key_fieldno = 0;

		/* check spaces indexes */
		for (size_t j = 0; space->index[j] != NULL; ++j) {
			typeof(space->index[j]) index = space->index[j];
			u32 key_part_count = 0;
			enum index_type index_type;

			/* check index bound */
			if (j >= BOX_INDEX_MAX) {
				/* maximum index in space reached */
				out_warning(0, "(space = %zu index = %zu) "
					    "too many indexed (%u maximum)", i, j, BOX_INDEX_MAX);
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

				if (key->fieldno >= BOX_FIELD_MAX) {
					/* maximum index in space reached */
					out_warning(0, "(space = %zu index = %zu) "
						    "invalid field number (%u maximum)",
						    i, j, BOX_FIELD_MAX);
					return -1;
				}

				/* key must has valid type */
				if (STR2ENUM(field_data_type, key->type) == field_data_type_MAX) {
					out_warning(0, "(space = %zu index = %zu) "
						    "unknown field data type: `%s'", i, j, key->type);
					return -1;
				}

				if (max_key_fieldno < key->fieldno + 1) {
					max_key_fieldno = key->fieldno + 1;
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
				/* check hash index */
				/* hash index must has single-field key */
				if (key_part_count != 1) {
					out_warning(0, "(space = %zu index = %zu) "
						    "hash index must has a single-field key", i, j);
					return -1;
				}
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
		if (max_key_fieldno > 0) {
			char *types = alloca(max_key_fieldno);
			memset(types, 0, max_key_fieldno);
			for (size_t j = 0; space->index[j] != NULL; ++j) {
				typeof(space->index[j]) index = space->index[j];
				for (size_t k = 0; index->key_field[k] != NULL; ++k) {
					typeof(index->key_field[k]) key = index->key_field[k];
					if (key->fieldno == -1)
						break;

					u32 f = key->fieldno;
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

