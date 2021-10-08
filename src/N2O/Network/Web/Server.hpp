#include <lean/lean.h>
#include <libwebsockets.h>
#include <iostream>
#include <queue>

typedef lean_object obj;

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
