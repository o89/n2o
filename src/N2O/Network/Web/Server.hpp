#include "lean/object.h"
#include "lean/io.h"
#include "lean/apply.h"
#include <libwebsockets.h>
#include <iostream>
#include <queue>

typedef lean::object obj;

enum MsgKind { Text, Binary };
struct Msg {
    enum MsgKind kind;
    size_t length;
    char* msg;
};

enum ConnectionType { Http, Wss };

struct n2o_userdata {
    obj* headers;
    ConnectionType method;
    std::queue<Msg>* pool;
};
