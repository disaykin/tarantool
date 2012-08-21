#ifndef tarantool_cfg_CFG_H
#define tarantool_cfg_CFG_H

#include <stdio.h>
#include <stdbool.h>
#include <sys/types.h>

#ifndef confetti_bool_t
#define confetti_bool_t char
#endif

/*
 * Autogenerated file, do not edit it!
 */

typedef struct tarantool_cfg_space_index_key_field {
	unsigned char __confetti_flags;

	int32_t	fieldno;
	char*	type;
} tarantool_cfg_space_index_key_field;

typedef struct tarantool_cfg_space_index {
	unsigned char __confetti_flags;

	char*	type;
	confetti_bool_t	unique;
	tarantool_cfg_space_index_key_field**	key_field;
} tarantool_cfg_space_index;

typedef struct tarantool_cfg_space {
	unsigned char __confetti_flags;

	confetti_bool_t	enabled;
	int32_t	cardinality;
	int32_t	estimated_rows;
	tarantool_cfg_space_index**	index;
} tarantool_cfg_space;

typedef struct tarantool_cfg {
	unsigned char __confetti_flags;


	/* username to switch to */
	char*	username;

	/*
	 * Local hot standby (if enabled, the server will run in hot
	 * standby mode, continuously fetching WAL records from wal_dir,
	 * until it is able to bind to the primary port.
	 * In local hot standby mode the server only accepts reads.
	 */
	confetti_bool_t	local_hot_standby;

	/*
	 * tarantool bind ip address, applies to master
	 * and replication ports. INADDR_ANY is the default value.
	 */
	char*	bind_ipaddr;

	/*
	 * save core on abort/assert
	 * deprecated; use ulimit instead
	 */
	confetti_bool_t	coredump;

	/*
	 * admin port
	 * used for admin's connections
	 */
	int32_t	admin_port;

	/* Replication clients should use this port (bind_ipaddr:replication_port). */
	int32_t	replication_port;

	/* Log verbosity, possible values: ERROR=1, CRIT=2, WARN=3, INFO=4(default), DEBUG=5 */
	int32_t	log_level;

	/* Size of slab arena in GB */
	double	slab_alloc_arena;

	/* Size of minimal allocation unit */
	int32_t	slab_alloc_minimal;

	/* Growth factor, each subsequent unit size is factor * prev unit size */
	double	slab_alloc_factor;

	/* working directory (daemon will chdir(2) to it) */
	char*	work_dir;

	/* Snapshot directory (where snapshots get saved/read) */
	char*	snap_dir;

	/* WAL directory (where WALs get saved/read) */
	char*	wal_dir;

	/* script directory (where init.lua is expected to be) */
	char*	script_dir;

	/* name of pid file */
	char*	pid_file;

	/*
	 * logger command will be executed via /bin/sh -c {}
	 * example: 'exec cronolog /var/log/tarantool/%Y-%m/%Y-%m-%d/tarantool.log'
	 * example: 'exec extra/logger.pl /var/log/tarantool/tarantool.log'
	 * when logger is not configured all logging going to STDERR
	 */
	char*	logger;

	/* make logging nonblocking, this potentially can lose some logging data */
	confetti_bool_t	logger_nonblock;

	/* delay between loop iterations */
	double	io_collect_interval;

	/* size of listen backlog */
	int32_t	backlog;

	/* network io readahead */
	int32_t	readahead;

	/* Do not write into snapshot faster than snap_io_rate_limit MB/sec */
	double	snap_io_rate_limit;

	/* Write no more rows in WAL */
	int32_t	rows_per_wal;

	/*
	 * OBSOLETE
	 * Starting from 1.4.5, this variable has no effect.
	 */
	int32_t	wal_writer_inbox_size;

	/*
	 * Defines fiber/data synchronization fsync(2) policy:
	 * "none":           does not write to WAL
	 * "write":          fibers wait for their data to be written to the log.
	 * "fsync":          fibers wait for their data, fsync(2) follows each write(2)
	 * "fsync_delay":    fibers wait for their data, fsync every N=wal_fsync_delay seconds,
	 * N=0.0 means no fsync (equivalent to wal_mode = "write");
	 */
	char*	wal_mode;

	/*
	 * Fsync WAL delay, only issue fsync if last fsync was wal_fsync_delay
	 * seconds ago.
	 * WARNING: actually, several last requests may stall fsync for much longer
	 */
	double	wal_fsync_delay;

	/*
	 * Delay, in seconds, between successive re-readings of wal_dir.
	 * The re-scan is necessary to discover new WAL files or snapshots.
	 */
	double	wal_dir_rescan_delay;

	/*
	 * Panic if there is an error reading a snapshot or WAL.
	 * By default, panic on any snapshot reading error and ignore errors
	 * when reading WALs.
	 */
	confetti_bool_t	panic_on_snap_error;
	confetti_bool_t	panic_on_wal_error;

	/* Statistics collector server */
	char*	stat;

	/* Interval of data pushing to a statistics collector server */
	int32_t	stat_interval;

	/*
	 * # BOX
	 * Primary port (where updates are accepted)
	 */
	int32_t	primary_port;

	/* Secondary port (where only selects are accepted) */
	int32_t	secondary_port;

	/* Warn about requests which take longer to process, in seconds. */
	double	too_long_threshold;

	/*
	 * A custom process list (ps) title string, appended after the standard
	 * program title.
	 */
	char*	custom_proc_title;

	/* Memcached protocol support is enabled if memcached_port is set */
	int32_t	memcached_port;

	/* space used for memcached emulation */
	int32_t	memcached_space;

	/* Memcached expiration is on if memcached_expire is set. */
	confetti_bool_t	memcached_expire;

	/* maximum rows to consider per expire loop iteration */
	int32_t	memcached_expire_per_loop;

	/* tarantool will try to iterate over all rows within this time */
	double	memcached_expire_full_sweep;

	/*
	 * Replication mode (if enabled, the server, once
	 * bound to the primary port, will connect to
	 * replication_source (ipaddr:port) and run continously
	 * fetching records from it.. In replication mode the server
	 * only accepts reads.
	 */
	char*	replication_source;
	tarantool_cfg_space**	space;
} tarantool_cfg;

#ifndef CNF_FLAG_STRUCT_NEW
#define CNF_FLAG_STRUCT_NEW	0x01
#endif
#ifndef CNF_FLAG_STRUCT_NOTSET
#define CNF_FLAG_STRUCT_NOTSET	0x02
#endif
#ifndef CNF_STRUCT_DEFINED
#define CNF_STRUCT_DEFINED(s) ((s) != NULL && ((s)->__confetti_flags & CNF_FLAG_STRUCT_NOTSET) == 0)
#endif

void init_tarantool_cfg(tarantool_cfg *c);

int fill_default_tarantool_cfg(tarantool_cfg *c);

void swap_tarantool_cfg(struct tarantool_cfg *c1, struct tarantool_cfg *c2);

void parse_cfg_file_tarantool_cfg(tarantool_cfg *c, FILE *fh, int check_rdonly, int *n_accepted, int *n_skipped, int *n_optional);

void parse_cfg_buffer_tarantool_cfg(tarantool_cfg *c, char *buffer, int check_rdonly, int *n_accepted, int *n_skipped, int *n_optional);

int check_cfg_tarantool_cfg(tarantool_cfg *c);

int dup_tarantool_cfg(tarantool_cfg *dst, tarantool_cfg *src);

void destroy_tarantool_cfg(tarantool_cfg *c);

char *cmp_tarantool_cfg(tarantool_cfg* c1, tarantool_cfg* c2, int only_check_rdonly);

typedef struct tarantool_cfg_iterator_t tarantool_cfg_iterator_t;
tarantool_cfg_iterator_t* tarantool_cfg_iterator_init();
char* tarantool_cfg_iterator_next(tarantool_cfg_iterator_t* i, tarantool_cfg *c, char **v);

#endif
