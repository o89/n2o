void read_headers(struct lws* wsi, n2o_userdata* user);
void send_msg(struct lws* wsi, n2o_userdata* user);
obj* read_msg(struct lws* wsi, n2o_userdata* user, char* in, size_t len);
void push_msg(struct lws* wsi, n2o_userdata* user, obj* res);

extern obj* n2o_handler;
extern int interrupted;
