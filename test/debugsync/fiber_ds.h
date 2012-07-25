/*
 * Copyright (C) 2010 Mail.RU
 * Copyright (C) 2010 Yuriy Vostrikov
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */



/****************************************************************
 * Debug synchronization facility allows to
 * 'insert' synchronization points into multi-threaded code.
 *
 * A a synchronization gets 'inserted' before a code
 * section one wants to test (in thread A). In order to 
 * put the system into a condition suitable for the test, 
 * other threads may need to execute their test-specific
 * code sections right before the tested sections executes
 * (in thread A).
 *
 * TODO: terminology and algorithm.
 *
 *
 *
 ****************************************************************/

#ifndef FIBERDS_H_20120703
#define FIBERDS_H_20120703

#include <sys/types.h>
#include <stdbool.h>

#ifdef NDEBUG

#	define  FDSYNC_ACTIVATE(activate)
#	define	FDSYNC_SET(name)
#	define  FDSYNC_ENABLE(name, enable)
#	define	FDSYNC_WAIT(name)
#	define	FDSYNC_UNBLOCK(name)

#else

#	define  FDSYNC_ACTIVATE(activate)	fds_activate(activate)
#	define	FDSYNC_SET(name)		(void)fds_exec(name)
#	define  FDSYNC_ENABLE(name, enable)	fds_enable(name, enable)
#	define	FDSYNC_WAIT(name)		fds_wait(name)
#	define	FDSYNC_UNBLOCK(name)		fds_unblock(name)

#endif

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initialize debug sync framework.
 *
 * @param active if false disables all debug sync operations.
 *
 * @return 0 if framework initialized, non-zero otherwise.
 */
void fds_init(bool activate);

/**
 * Release resources allocated for debug sync framework.
 */
void fds_destroy();

/**
 * Toggle the framework's status.
 *
 * @param active [dis]allows debug sync operations.
 */
int fds_activate(bool activate);

/**
 * Enable or disable an existing syn point.
 *
 * @param point_name name of the sync point.
 * @param enable enable or disable sync point's execution.
 *
 * @return 0 if the sync point's statue was successfully changed.
 */
int fds_enable(const char *point_name, bool enable);

/**
 * Disable all known sync points.
 */
void fds_disable_all();

/**
 * Execute (pass through) a sync point.
 *
 * @param point_name name of the sync point.
 *
 * @return 0 if the sync point has been passed successfully, non-zero otherwise.
 */
int fds_exec(const char *point_name);

/**
 * Wait for a sync point (existing or a new one) to be reached.
 *
 * @param point_name name of the sync point.
 *
 * @return 0 if the sync point was successfully reached, non-zero otherwise.
 */
int fds_wait(const char *point_name);

/**
 * Attempt to unlock a sync point holding for a waiting block.
 *
 * @param point_name name of the sync point.
 *
 * @return 0 if an event to unblock has been raised successfully, non-zero otherwise.
 */
int fds_unlock(const char *point_name);

/**
 * Output (into a buffer) framework info/statistics in human-readable form.
 *
 * @param out destination buffer.
 */
void fds_info(struct tbuf *out);

#ifdef __cplusplus
}
#endif

#endif /* DEBUGSYNC_H_20120703 */
/* __EOF__ */
