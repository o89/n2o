#include "runtime/object.h"
#include "runtime/io.h"
#include "runtime/apply.h"
#include <libwebsockets.h>
#include <iostream>
#include <queue>

typedef lean::object obj;

struct n2o_userdata {
    lws* wsi;
    char* headers;
    uint8_t headers_count;
    size_t headers_length;
    std::queue<char*>* pool;
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

obj* get_headers(uint8_t count, char* headers) {
    char* ptr = headers;

    obj* zero = prod(lean::mk_string(""), lean::mk_string(""));
    obj* arr = lean::mk_array(lean::mk_nat_obj(count), zero);

    for (int i = 0; i < count; i++) {
        auto name = get_string(ptr); ptr += strlen(name) + 1;
        auto value = get_string(ptr); ptr += strlen(value) + 1;

        arr = lean::array_set(
            arr, lean::mk_nat_obj(i),
            prod(lean::mk_string(name), lean::mk_string(value))
        );

        free(name); free(value);
    }
    ptr = nullptr;

    return arr;
}

auto lean_send_message(obj* user, obj* msg, obj* r) {
    auto ref = (n2o_userdata*) user;

    auto res = (char*) malloc(lean::string_len(msg) + 1);
    strcpy(res, lean::string_cstr(msg));

    ref->pool->push(res);
    lws_callback_on_writable(ref->wsi);

    return lean::set_io_result(r, lean::box(0));
}

static int callback_n2o(struct lws *wsi,
                        enum lws_callback_reasons reason,
                        void *user, void *in, size_t len) {
    auto userdata = (n2o_userdata*) user;

    switch (reason) {
        case LWS_CALLBACK_RECEIVE: {
            auto headers = get_headers(userdata->headers_count, userdata->headers);

            auto write = lean::alloc_closure(lean_send_message, 1);
            closure_set(write, 0, (obj*) user);

            auto socket = lean::alloc_cnstr(0, 3, 0);
            lean::cnstr_set(socket, 0, lean::mk_string((char *) in));
            lean::cnstr_set(socket, 1, write);
            lean::cnstr_set(socket, 2, headers);

            lean::apply_2(n2o_handler, socket, lean::io_mk_world());

            break;
        }

        case LWS_CALLBACK_SERVER_WRITEABLE: {
            if (!userdata->pool->empty()) {
                auto str = userdata->pool->front();
                printf("[debug] pool: %s\n", str);
                auto length = strlen(str);
                userdata->pool->pop();

                auto buff = (char*) malloc(length + LWS_PRE + 1);
                strcpy(&buff[LWS_PRE], str);
                free(str);

                lws_write(wsi, (unsigned char*) &buff[LWS_PRE], length, LWS_WRITE_TEXT);
                free(buff);
            }
            break;
        }

        case LWS_CALLBACK_FILTER_PROTOCOL_CONNECTION: {
            userdata->wsi = wsi;
            userdata->pool = new std::queue<char*>;
            userdata->headers_length = 0;
            userdata->headers_count = 0;

            for (int i = 0; i < WSI_TOKEN_COUNT; i++) {
                auto token = (enum lws_token_indexes) i;
                int len = lws_hdr_total_length(wsi, token);
                if (len > 0) {
                    auto name = (const char*) lws_token_to_string(token);

                    userdata->headers_length += strlen(name) + 1;
                    userdata->headers_length += len + 1;
                }
            }

            userdata->headers = (char*) malloc(userdata->headers_length);
            memset(userdata->headers, 0, userdata->headers_length);

            auto ptr = userdata->headers;
            for (int i = 0; i < WSI_TOKEN_COUNT; i++) {
                auto token = (enum lws_token_indexes) i;
                int len = lws_hdr_total_length(wsi, token);

                if (len > 0) {
                    auto name = (const char*) lws_token_to_string(token);
                    size_t name_length = strlen(name);

                    memcpy(ptr, name, name_length);
                    ptr += name_length + 1; *ptr = '\0';

                    lws_hdr_copy(wsi, ptr, len + 1, token);
                    ptr += len + 1;

                    userdata->headers_count++;
                }
            }
            ptr = nullptr;

            break;
        }

        case LWS_CALLBACK_CLOSED: {
            free(userdata->headers);

            while (!userdata->pool->empty()) {
                free(userdata->pool->front());
                userdata->pool->pop();
            }
            delete userdata->pool;
            break;
        }
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
    return lean::set_io_result(r, lean::box(0));
}

static int interrupted;

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
