#include "Server.hpp"
#include "Callback.hpp"

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
            auto socket = lean_alloc_ctor(0, 2, 0);
            auto msg = read_msg(wsi, userdata, (char*) in, len);
            lean_ctor_set(socket, 0, msg);
            lean_ctor_set(socket, 1, userdata->headers);

            auto res = lean_apply_1(n2o_handler, socket);
            push_msg(wsi, userdata, res);

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
            lean_free_object(userdata->headers);
            break;
        }

        default: break;
    }
    return 0;
}

static int callback(struct lws *wsi,
                    enum lws_callback_reasons reason,
                    void *user, void *in, size_t len) {
    auto userdata = (n2o_userdata*) user;
    if (!userdata) return 0; // ???

    if (reason == LWS_CALLBACK_FILTER_PROTOCOL_CONNECTION) {
        auto length = lws_hdr_total_length(wsi, WSI_TOKEN_UPGRADE);
        auto upgrade = (char*) malloc(length + 1);
        lws_hdr_copy(wsi, upgrade, length + 1, WSI_TOKEN_UPGRADE);
        upgrade[length] = (char) 0;
        userdata->method = strcmp(upgrade, "websocket") ?
            ConnectionType::Http : ConnectionType::Wss;
        free(upgrade);
    }

    return (userdata->method == ConnectionType::Wss) ?
        callback_n2o(wsi, reason, user, in, len) :
        lws_callback_http_dummy(wsi, reason, user, in, len);
}

static struct lws_protocols protocols[] = {
    { "", callback, sizeof(n2o_userdata) },
    { NULL, NULL, 0 }
};

extern "C" obj* lean_set_handler(obj* f, obj* r) {
    n2o_handler = f;
    lean_mark_persistent(f);
    return lean_io_result_mk_ok(lean_box_uint32(0));
}

extern "C" obj* lean_stop_server(obj* r) {
    interrupted = 1;
    return lean_io_result_mk_ok(lean_box_uint32(0));
}

extern "C" obj* lean_run_server(obj* addr, uint16_t port, obj* r) {
    interrupted = 0;

    struct lws_context *context;
    const char *host = lean_string_cstr(addr);

    struct lws_context_creation_info info;
    memset(&info, 0, sizeof(info));

    info.port = port;
    info.vhost_name = host;
    info.mounts = &mounts;
    info.protocols = protocols;

    context = lws_create_context(&info);
    if (!context) return lean_io_result_mk_error(lean_mk_string("lws init failed"));

    printf("Started server at %s:%d\n", host, port);

    while (!interrupted) lws_service(context, 0);

    lws_context_destroy(context);

    return lean_io_result_mk_ok(lean_box_uint32(0));
}
