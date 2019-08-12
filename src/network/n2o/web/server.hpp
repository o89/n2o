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