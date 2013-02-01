#ifndef TARANTOOL_PTHREAD_H_INCLUDED
#define TARANTOOL_PTHREAD_H_INCLUDED
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

#include "config.h"

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

#if defined(HAVE_NON_C99_PTHREAD_H)
/*
 * Old versions of glibc (pre-2006) use "extern __inline" for this function.
 * This definition, of course, does not work properly with C99 mode when
 * multiple compilation units are used.
 *
 * By defining "static inline" prototype we force GCC think that
 * this method is "static" and no global symbols must be produced for it.
 *
 * See http://gcc.gnu.org/ml/gcc-patches/2006-11/msg01030.html
 *     http://gcc.gnu.org/ml/gcc-patches/2008-07/msg02449.html
 */
struct __pthread_cleanup_frame;
static inline void
__pthread_cleanup_routine(struct __pthread_cleanup_frame *__frame);

#define __inline
#endif /* HAVE_NON_C99_PTHREAD_H */

#include <pthread.h>

#include <util.h>
#include <say.h>

/**
 * Assert on any pthread* error in debug mode. In release,
 * write into the log file where and what has failed.
 *
 * Still give the user an opportunity to manually
 * check for error, by returning the pthread_* 
 * function status.
 */

#define tt_pthread_error(e)			\
	if (e != 0)				\
		say_error("%s error %d", __func__, e);\
	assert(e == 0);				\
	e

/**
 * Debug/logging friendly wrappers around pthread
 * functions.
 */

#define tt_pthread_mutex_init(mutex, attr)	\
({	int e = pthread_mutex_init(mutex, attr);\
	tt_pthread_error(e);			\
})

#define tt_pthread_mutex_destroy(mutex)		\
({	int e = pthread_mutex_destroy(mutex);	\
	tt_pthread_error(e);			\
})

#define tt_pthread_mutex_lock(mutex)		\
({	int e = pthread_mutex_lock(mutex);	\
	say_debug("%s: locking %s", __func__, #mutex);\
	tt_pthread_error(e);\
})

#define tt_pthread_mutex_trylock(mutex)		\
({	int e = pthread_mutex_trylock(mutex);	\
	if (e != 0 && e != EBUSY)		\
		say_error("%s error %d at %s:%d", __func__, e, __FILE__, __LINE__);\
	assert(e == 0 || e == EBUSY);		\
	e					\
})

#define tt_pthread_mutex_unlock(mutex)		\
({	int e = pthread_mutex_unlock(mutex);	\
	say_debug("%s: unlocking %s", __func__, #mutex);\
	tt_pthread_error(e);			\
})

#define tt_pthread_mutex_destroy(mutex)		\
({	int e = pthread_mutex_destroy(mutex);	\
	tt_pthread_error(e);			\
})

#define tt_pthread_mutexattr_init(attr)		\
({	int e = pthread_mutexattr_init(attr);	\
	tt_pthread_error(e);			\
})

#define tt_pthread_mutexattr_destroy(attr)	\
({	int e = pthread_mutexattr_destroy(attr);\
	tt_pthread_error(e);			\
})

#define tt_pthread_mutexattr_gettype(attr, type)\
({	int e = pthread_mutexattr_gettype(attr, type);\
	tt_pthread_error(e);			\
})

#define tt_pthread_mutexattr_settype(attr, type)\
({	int e = pthread_mutexattr_settype(attr, type);\
	tt_pthread_error(e);			\
})

#define tt_pthread_condattr_init(attr)		\
({	int e = pthread_condattr_init(attr);	\
	tt_pthread_error(e);			\
})

#define tt_pthread_condattr_destroy(attr)	\
({ int e = pthread_condattr_destroy(attr);	\
	tt_pthread_error(e);			\
})

#define tt_pthread_cond_init(cond, attr)	\
({	int e = pthread_cond_init(cond, attr);	\
	tt_pthread_error(e);			\
})

#define tt_pthread_cond_destroy(cond)		\
({	int e = pthread_cond_destroy(cond);	\
	tt_pthread_error(e);			\
})

#define tt_pthread_cond_signal(cond)		\
({	int e = pthread_cond_signal(cond);	\
	tt_pthread_error(e);			\
})

#define tt_pthread_cond_wait(cond, mutex)	\
({	int e = pthread_cond_wait(cond, mutex);\
	tt_pthread_error(e);			\
})

#define tt_pthread_cond_timedwait(cond, mutex, timeout)	\
({	int e = pthread_cond_timedwait(cond, mutex, timeout);\
	if (ETIMEDOUT != e)                           \
		say_error("%s error %d", __func__, e);\
	assert(e == 0 || e == ETIMEDOUT);             \
	e                                             \
})

#define tt_pthread_once(control, function)	\
({	int e = pthread_once(control, function);\
	tt_pthread_error(e);			\
})

#define tt_pthread_atfork(prepare, parent, child)\
({	int e = pthread_atfork(prepare, parent, child);\
	tt_pthread_error(e);			\
})

/** Make sure the created thread blocks all signals,
 * they are handled in the main thread.
 */
#define tt_pthread_create(thread, attr, run, arg)	\
({	sigset_t set, oldset;				\
	sigfillset(&set);				\
	pthread_sigmask(SIG_BLOCK, &set, &oldset);	\
	int e = pthread_create(thread, attr, run, arg);	\
	pthread_sigmask(SIG_SETMASK, &oldset, NULL);	\
	tt_pthread_error(e);				\
})

#define tt_pthread_join(thread, ret)			\
({	int e = pthread_join(thread, ret);		\
	tt_pthread_error(e);				\
})

#if defined(__cplusplus)
} /* extern "C" */
#endif /* defined(__cplusplus) */

#endif /* TARANTOOL_PTHREAD_H_INCLUDED */
