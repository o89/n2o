#include "server.hpp"

obj* n2o_handler;
int interrupted;

obj* prod(obj* fst, obj* snd) {
    obj* tuple = lean::alloc_cnstr(0, 2, 0);
    lean::cnstr_set(tuple, 0, fst);
    lean::cnstr_set(tuple, 1, snd);

    return tuple;
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
    if (lean::obj_tag(res) == 0) { // error
        printf("%s\n", lean::string_cstr(lean::cnstr_get(res, 0)));
        interrupted = 1;
    } else if (lean::obj_tag(res) == 1) { // warning
        printf("%s\n", lean::string_cstr(lean::cnstr_get(res, 0)));
    } else if (lean::obj_tag(res) == 2) { // reply
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
