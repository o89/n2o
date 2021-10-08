#include "Server.hpp"

obj* n2o_handler;
int interrupted;

obj* prod(obj* fst, obj* snd) {
    obj* tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, fst);
    lean_ctor_set(tuple, 1, snd);

    return tuple;
}

void read_headers(struct lws* wsi, n2o_userdata* user) {
    uint64_t count = 0;
    for (int i = 0; i < WSI_TOKEN_COUNT; i++) {
        auto token = (enum lws_token_indexes) i;
        if (lws_hdr_total_length(wsi, token) > 0) count++;
    }

    auto zero = prod(lean_mk_string(""), lean_mk_string(""));
    user->headers = lean_mk_array(lean_uint64_to_nat(count), zero);
    count = 0;

    for (int i = 0; i < WSI_TOKEN_COUNT; i++) {
        auto token = (enum lws_token_indexes) i;
        int len = lws_hdr_total_length(wsi, token);

        if (len > 0) {
            auto name = (const char*) lws_token_to_string(token);

            auto value = (char*) malloc(len + 1);
            lws_hdr_copy(wsi, value, len + 1, token);
            value[len] = '\0';

            lean_array_cptr(user->headers)[count] =
                prod(lean_mk_string(name), lean_mk_string(value));
            free(value);
            count++;
        }
    }
    lean_mark_persistent(user->headers);
}

void send_msg(struct lws* wsi, n2o_userdata* user) {
    if (!user->pool->empty()) {
        auto str = user->pool->front();
        user->pool->pop();

        auto buff = (char*) malloc(LWS_PRE + str.length);
        memcpy(&buff[LWS_PRE], str.msg, str.length); free(str.msg);

        lws_write(wsi, (unsigned char*) &buff[LWS_PRE], str.length,
                  (str.kind == Text) ? LWS_WRITE_TEXT : LWS_WRITE_BINARY);
        free(buff);
    }
}

obj* read_msg(struct lws* wsi, n2o_userdata* user, char* in, size_t len) {
    obj* msg;
    if (lws_frame_is_binary(wsi)) {
        msg = lean_alloc_ctor(1, 1, 0);

        auto buff = lean_alloc_sarray(sizeof(char), len, len);
        memcpy(lean_sarray_cptr(buff), in, len);
        lean_ctor_set(msg, 0, buff);
    } else {
        msg = lean_alloc_ctor(0, 1, 0);
        auto str = (char*) malloc(len + 1);
        memcpy(str, in, len); str[len] = '\0';

        lean_ctor_set(msg, 0, lean_mk_string(str)); free(str);
    }

    return msg;
}

void push_msg(struct lws* wsi, n2o_userdata* user, obj* res) {
    auto tag = lean_obj_tag(res);

    switch (tag) {
        case 0: { // error
            printf("%s\n", lean_string_cstr(lean_ctor_get(res, 0)));
            interrupted = 1;
	    break;
	}
        case 1: { // warning
            printf("%s\n", lean_string_cstr(lean_ctor_get(res, 0)));
	    break;
	}
	case 2: { // reply
            auto reply = lean_ctor_get(res, 0);

            if (lean_obj_tag(reply) == 0) {
                // free(msg); calls `send_msg` or callback on close
                auto text = lean_ctor_get(reply, 0);
		auto length = lean_string_size(text);
                auto msg = (char*) malloc(length);
                strcpy(msg, lean_string_cstr(text));

                user->pool->push({ Text, length, msg });
                lws_callback_on_writable(wsi);
            } else {
                auto arr = lean_ctor_get(reply, 0);
                auto size = lean_sarray_size(arr);

                auto msg = (char*) malloc(size);
                for (size_t i = 0; i < size; i++)
                    msg[i] = lean_byte_array_get(arr, lean_box(i));

                user->pool->push({ Binary, size, msg });
                lws_callback_on_writable(wsi);
            }
        }
    }
}
