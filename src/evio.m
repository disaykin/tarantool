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
#include "evio.h"
#include <stdio.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>

#if EV_MULTIPLICITY
#error libev with enabled EV_MULTIPLICITY is not supported yet
#endif

#define BIND_RETRY_DELAY 0.1

/** Note: this function does not throw. */
void
evio_close(struct ev_io *evio)
{
	/* Stop I/O events. Safe to do even if not started. */
	ev_io_stop(evio);
	/* Close the socket. */
	close(evio->fd);
	/* Make sure evio_is_active() returns a proper value. */
	evio->fd = -1;
}

/**
 * Create an endpoint for communication.
 * Set socket as non-block and apply protocol specific options.
 */
void
evio_socket(struct ev_io *coio, int domain, int type, int protocol)
{
	assert(coio->fd == -1);
	/* Don't leak fd if setsockopt fails. */
	coio->fd = sio_socket(domain, type, protocol);
	if (type == SOCK_STREAM) {
		evio_setsockopt_tcp(coio->fd);
	} else {
		sio_setfl(coio->fd, O_NONBLOCK, 1);
	}
}


/** Set common tcp socket client options. */
void
evio_setsockopt_tcp(int fd)
{
	int on = 1;
	/* In case this throws, the socket is not leaked. */
	sio_setfl(fd, O_NONBLOCK, on);
	/* SO_KEEPALIVE to ensure connections don't hang
	 * around for too long when a link goes away.
	 */
	sio_setsockopt(fd, SOL_SOCKET, SO_KEEPALIVE,
		       &on, sizeof(on));
	/*
	 * Lower latency is more important than higher
	 * bandwidth, and we usually write entire
	 * request/response in a single syscall.
	 */
	sio_setsockopt(fd, IPPROTO_TCP, TCP_NODELAY,
		       &on, sizeof(on));
}

/** Set tcp options for server sockets. */
void
evio_setsockopt_tcpserver(int fd)
{
	int on = 1;
	/* In case this throws, the socket is not leaked. */
	sio_setfl(fd, O_NONBLOCK, on);
	/* Allow reuse local adresses. */
	sio_setsockopt(fd, SOL_SOCKET, SO_REUSEADDR,
		       &on, sizeof(on));
	sio_setsockopt(fd, SOL_SOCKET, SO_KEEPALIVE,
		       &on, sizeof(on));

	/* Send all buffered messages on socket before take
	 * control out from close(2) or shutdown(2). */
	struct linger linger = { 0, 0 };

	sio_setsockopt(fd, SOL_SOCKET, SO_LINGER,
		       &linger, sizeof(linger));
}

/**
 * Bind to a first address in addrinfo list and initialize coio
 * with bound socket.
 */
void
evio_bind_addrinfo(struct ev_io *evio, struct addrinfo *ai)
{
	assert(! evio_is_active(evio));
	int fd = -1;
	while (ai) {
		struct sockaddr_in *addr = (struct sockaddr_in *)ai->ai_addr;
		@try {
			fd = sio_socket(ai->ai_family, ai->ai_socktype,
					ai->ai_protocol);
			evio_setsockopt_tcpserver(fd);
			if (sio_bind(fd, addr, ai->ai_addrlen) == 0) {
				evio->fd = fd;
				return; /* success. */
			}
			assert(errno == EADDRINUSE);
		} @catch (SocketError *e) {
			if (ai->ai_next == NULL) {
				close(fd);
				@throw;
			}
		}
		close(fd);
		ai = ai->ai_next;
	}
	tnt_raise(SocketError, :evio->fd in:"evio_bind_addrinfo()");
}

static inline int
evio_service_port(struct evio_service *service)
{
	return ntohs(service->addr.sin_port);
}

/**
 * A callback invoked by libev when acceptor socket is ready.
 * Accept the socket, initialize it and pass to the on_accept
 * callback.
 */
static void
evio_service_accept_cb(ev_io *watcher,
		       int revents __attribute__((unused)))
{
	struct evio_service *service = watcher->data;
	int fd = -1;

	@try {
		struct sockaddr_in addr;
		socklen_t addrlen = sizeof(addr);
		fd = sio_accept(service->ev.fd, &addr, &addrlen);

		if (fd < 0) /* EAGAIN, EWOULDLOCK, EINTR */
			return;
		/* set common tcp options */
		evio_setsockopt_tcp(fd);
		/*
		 * Invoke the callback and pass it the accepted
		 * socket.
		 */
		service->on_accept(service, fd, &addr);

	} @catch (tnt_Exception *e) {
		if (fd >= 0)
			close(fd);
		[e log];
	}
}

/** Try to bind and listen on the configured port.
 *
 * Throws an exception if error.
 * Returns -1 if the address is already in use, and one
 * needs to retry binding.
 */
static int
evio_service_bind_and_listen(struct evio_service *service)
{
	/* Create a socket. */
	int fd = sio_socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);

	@try {
		evio_setsockopt_tcpserver(fd);

		if (sio_bind(fd, &service->addr, sizeof(service->addr)) ||
		    sio_listen(fd)) {
			assert(errno == EADDRINUSE);
			close(fd);
			return -1;
		}
		say_info("bound to port %i", evio_service_port(service));

		/* Invoke on_bind callback if it is set. */
		if (service->on_bind)
			service->on_bind(service->on_bind_param);

	} @catch (tnt_Exception *e) {
		close(fd);
		@throw;
	}
	/* Register the socket in the event loop. */
	ev_io_set(&service->ev, fd, EV_READ);
	ev_io_start(&service->ev);
	return 0;
}

/** A callback invoked by libev when sleep timer expires.
 *
 * Retry binding. On success, stop the timer. If the port
 * is still in use, pause again.
 */
static void
evio_service_timer_cb(ev_timer *watcher, int revents __attribute__((unused)))
{
	struct evio_service *service = watcher->data;
	assert(! ev_is_active(&service->ev));

	if (evio_service_bind_and_listen(service) == 0)
		ev_timer_stop(watcher);
}

void
evio_service_init(struct evio_service *service, const char *name,
		  const char *host, int port,
		  void (*on_accept)(struct evio_service *, int,
				    struct sockaddr_in *),
		  void *on_accept_param)
{
	memset(service, 0, sizeof(struct evio_service));
	snprintf(service->name, sizeof(service->name), "%s", name);

	service->addr.sin_family = AF_INET;
	service->addr.sin_port = htons(port);
	if (strcmp(host, "INADDR_ANY") == 0) {
		service->addr.sin_addr.s_addr = INADDR_ANY;
	} else if (inet_aton(host, &service->addr.sin_addr) == 0) {
		tnt_raise(SocketError, :"invalid address for bind: %s",
			  host);
	}
	service->on_accept = on_accept;
	service->on_accept_param = on_accept_param;
	/*
	 * Initialize libev objects to be able to detect if they
	 * are active or not in evio_service_stop().
	 */
	ev_init(&service->ev, evio_service_accept_cb);
	ev_init(&service->timer, evio_service_timer_cb);
	service->timer.data = service->ev.data = service;
}

/**
 * Try to bind and listen. If the port is in use,
 * say a warning, and start the timer which will retry
 * binding periodically.
 */
void
evio_service_start(struct evio_service *service)
{
	assert(! ev_is_active(&service->ev));

	if (evio_service_bind_and_listen(service)) {
		/* Try again after a delay. */
		say_warn("port %i is already in use, will "
			 "retry binding after %lf seconds.",
			 evio_service_port(service), BIND_RETRY_DELAY);

		ev_timer_set(&service->timer,
			     BIND_RETRY_DELAY, BIND_RETRY_DELAY);
		ev_timer_start(&service->timer);
	}
}

/** It's safe to stop a service which is not started yet. */
void
evio_service_stop(struct evio_service *service)
{
	if (! ev_is_active(&service->ev)) {
		ev_timer_stop(&service->timer);
	} else {
		ev_io_stop(&service->ev);
		close(service->ev.fd);
	}
}
