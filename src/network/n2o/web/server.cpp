#include "runtime/object.h"
#include "runtime/io.h"
#include "runtime/apply.h"
#include <libwebsockets.h>
#include <iostream>
#include <queue>

typedef lean::object obj;

enum MsgKind { Text, Binary };
struct Msg {
    enum MsgKind kind;
    char* msg;
};

struct n2o_userdata {
    obj* headers;
    std::queue<Msg>* pool;
};

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

obj* n2o_handler;

static int interrupted;

obj* prod(obj* fst, obj* snd) {
    obj* tuple = lean::alloc_cnstr(0, 2, 0);
    lean::cnstr_set(tuple, 0, fst);
    lean::cnstr_set(tuple, 1, snd);

    return tuple;
}

char* get_string(char* ptr) {
    size_t len = 0;
    while (*(ptr + len) != '\0') len++;

    auto res = (char*) malloc(len + 1);
    memcpy(res, ptr, len + 1);
    return res;
}

void read_headers(struct lws* wsi, n2o_userdata* user) {
    int count = 0;
    for (int i = 0; i < WSI_TOKEN_COUNT; i++) {
        auto token = (enum lws_token_indexes) i;
        if (lws_hdr_total_length(wsi, token) > 0) count++;
    }

    auto zero = prod(lean::mk_string(""), lean::mk_string(""));
    user->headers = lean::mk_array(lean::mk_nat_obj(count), zero);
    count = 0;

    for (int i = 0; i < WSI_TOKEN_COUNT; i++) {
        auto token = (enum lws_token_indexes) i;
        int len = lws_hdr_total_length(wsi, token);

        if (len > 0) {
            auto name = (const char*) lws_token_to_string(token);

            auto value = (char*) malloc(len + 1);
            lws_hdr_copy(wsi, value, len + 1, token);
            value[len] = '\0';

            user->headers = lean::array_set(
                user->headers, lean::mk_nat_obj(count),
                prod(lean::mk_string(name), lean::mk_string(value))
            ); free(value);
            lean::mark_persistent(user->headers);
            count++;
        }
    }
}

void send_msg(struct lws* wsi, n2o_userdata* user) {
    if (!user->pool->empty()) {
        auto str = user->pool->front();

        auto length = strlen(str.msg);
        if (str.kind == Text) length++; // leading zero

        user->pool->pop();

        auto buff = (char*) malloc(LWS_PRE + length);
        memcpy(&buff[LWS_PRE], str.msg, length); free(str.msg);

        lws_write(wsi, (unsigned char*) &buff[LWS_PRE], length,
                  (str.kind == Text) ? LWS_WRITE_TEXT : LWS_WRITE_BINARY);
        free(buff);
    }
}

obj* read_msg(struct lws* wsi, n2o_userdata* user, char* in, size_t len) {
    obj* msg;
    if (lws_frame_is_binary(wsi)) {
        msg = lean::alloc_cnstr(1, 1, 0);

        auto buff = lean::mk_array(lean::mk_nat_obj(len), lean::box(0));
        for (size_t i = 0; i < len; i++)
            buff = lean::array_set(buff, lean::mk_nat_obj(i), lean::box(in[i]));
        lean::cnstr_set(msg, 0, buff);
    } else {
        msg = lean::alloc_cnstr(0, 1, 0);
        auto str = (char*) malloc(len + 1);
        memcpy(str, in, len); str[len] = '\0';

        lean::cnstr_set(msg, 0, lean::mk_string(str)); free(str);
    }

    return msg;
}

void push_msg(struct lws* wsi, n2o_userdata* user, obj* res) {
    if (lean::obj_tag(res) == 0) {
        printf("%s\n", lean::string_cstr(lean::cnstr_get(res, 0)));
        interrupted = 1;
    } else if (lean::obj_tag(res) == 1) {
        auto reply = lean::cnstr_get(res, 0);

        if (lean::obj_tag(reply) == 0) {
            // free(msg); calls `send_msg` or callback on close
            auto text = lean::cnstr_get(reply, 0);
            auto msg = (char*) malloc(lean::string_len(text) + 1);
            strcpy(msg, lean::string_cstr(text));

            user->pool->push({ Text, msg });
            lws_callback_on_writable(wsi);
        } else {
            auto arr = lean::cnstr_get(reply, 0);
            auto size = lean::array_size(arr);

            auto msg = (char*) malloc(size + 1);
            for (size_t i = 0; i < size; i++)
                msg[i] = lean::unbox(lean::array_get(arr, i));
            msg[size] = '\0';

            user->pool->push({ Binary, msg });
            lws_callback_on_writable(wsi);
        }
    }
}

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
    info.ws_ping_pong_interval = 1;
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
