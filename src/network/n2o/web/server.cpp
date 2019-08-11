#include "server.hpp"
#include "callback.hpp"

static const struct lws_http_mount mounts = {
    /* .mount_next */            NULL,
    /* .mountpoint */            "/",
    /* .origin */                ".",
    /* .def */                   NULL,
    /* .protocol */              NULL,
    /* .cgienv */                NULL,
    /* .extra_mimetypes */       NULL,
    /* .interpret */             NULL,
    /* .cgi_timeout */           0,
    /* .cache_max_age */         0,
    /* .auth_mask */             0,
    /* .cache_reusable */        0,
    /* .cache_revalidate */      0,
    /* .cache_intermediaries */  0,
    /* .origin_protocol */       LWSMPRO_FILE,
    /* .mountpoint_len */        1,
    /* .basic_auth_login_file */ NULL,
};

static int callback_n2o(struct lws *wsi,
                        enum lws_callback_reasons reason,
                        void *user, void *in, size_t len) {
    auto userdata = (n2o_userdata*) user;

    switch (reason) {
        case LWS_CALLBACK_RECEIVE: {
            auto socket = lean::alloc_cnstr(0, 2, 0);

            lean::cnstr_set(socket, 0, read_msg(wsi, userdata, (char*) in, len));
            lean::cnstr_set(socket, 1, userdata->headers);

            push_msg(wsi, userdata, lean::apply_1(n2o_handler, socket));
            break;
        }

        case LWS_CALLBACK_SERVER_WRITEABLE: {
            send_msg(wsi, userdata);
            break;
        }

        case LWS_CALLBACK_FILTER_PROTOCOL_CONNECTION: {
            userdata->pool = new std::queue<Msg>;
            read_headers(wsi, userdata);
            break;
        }

        case LWS_CALLBACK_CLOSED: {
            while (!userdata->pool->empty()) {
                free(userdata->pool->front().msg);
                userdata->pool->pop();
            }
            delete userdata->pool;
            break;
        }

        default: break;
    }
    return 0;
}

static struct lws_protocols protocols[] = {
    { "http", lws_callback_http_dummy, 0 },
    { "n2o", callback_n2o, sizeof(n2o_userdata) },
    { NULL, NULL, 0 }
};

extern "C" obj* lean_set_handler(obj* f, obj* r) {
    n2o_handler = f;
    lean::mark_persistent(f);
    return lean::set_io_result(r, lean::box(0));
}

extern "C" obj* lean_stop_server(obj* r) {
    interrupted = 1;
    return lean::set_io_result(r, lean::box(0));
}

extern "C" obj* lean_run_server(obj* addr, lean::uint16 port, obj* r) {
    interrupted = 0;

    struct lws_context *context;
    const char *host = lean::string_cstr(addr);    

    struct lws_context_creation_info info;
    memset(&info, 0, sizeof(info));

    info.port = port;
    info.vhost_name = host;
    info.mounts = &mounts;
    info.protocols = protocols;
    info.ws_ping_pong_interval = 0;
    info.options =
        LWS_SERVER_OPTION_HTTP_HEADERS_SECURITY_BEST_PRACTICES_ENFORCE;

    context = lws_create_context(&info);
    if (!context) {
        return lean::set_io_error(r, lean::mk_string("lws init failed"));
    }

    printf("Started server at %s:%d\n", host, port);

    while (!interrupted) lws_service(context, 10);

    lws_context_destroy(context);

    return lean::set_io_result(r, lean::box(0));
}
