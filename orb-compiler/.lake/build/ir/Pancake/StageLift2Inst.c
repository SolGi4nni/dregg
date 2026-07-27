// Lean compiler output
// Module: Pancake.StageLift2Inst
// Imports: public import Init public meta import Init public import Pancake.StageLift2
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lp_orb_x2dcompiler_Pancake_StageProg_str(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqBitVec___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_StageLift2_addHeadersR(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_StageLift2_stampSpec(lean_object*, lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_StageLift2_stampSetSpec(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetProg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec___lam__0___boxed(lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Content-Type"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "text/html"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "text/event-stream"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Set-Cookie"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "sid=1; Path=/"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "X-Request-Id"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "X-Forwarded-For"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Access-Control-Allow-Origin"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Date"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Content-Language"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Vary"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Accept-Language"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_dashTypeSpec(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_spaTypeSpec(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseHeadSpec(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieSpec(lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec___lam__0___boxed(lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_proxyProtoSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_corsSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateSpec(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_securityHeadersSpec(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Content Too Large"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "content too large\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Service Unavailable"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "per-source connection limit reached\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Request Header Fields Too Large"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "request header fields too large\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "URI Too Long"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "uri too long\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Too Many Requests"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "aggregated request limit exceeded\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "rate limit exceeded\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Request Timeout"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "request header timeout\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Not Modified"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Last-Modified"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__3;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Mon, 01 Jan 2024 00:00:00 GMT"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__4_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__8;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Bad Request"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bad request\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Expectation Failed"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expectation failed\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Not Implemented"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "not implemented\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "HTTP Version Not Supported"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "http version not supported\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Misdirected Request"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "misdirected request\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Unauthorized"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "WWW-Authenticate"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__3;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Bearer"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__4_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__7;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "invalid or missing bearer token"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__8_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__10;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "authentication required"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "auth subrequest denied\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Forbidden"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Internal Server Error"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "auth subrequest failed\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardResp500;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardReasonOf(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardReasonOf___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardDenyResp(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "X-Frame-Options"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "DENY"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__4;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "X-Content-Type-Options"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__5_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__6;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nosniff"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__7_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__11;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy;
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instDecidableEqBitVec___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(8) << 1) | 1))} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__2;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetProg(lean_object* v_p_1_, lean_object* v_nvs_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lp_orb_x2dcompiler_Pancake_StageLift2_addHeadersR(v_nvs_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_5_, 0, v_p_1_);
lean_ctor_set(v___x_5_, 1, v___x_3_);
lean_ctor_set(v___x_5_, 2, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetFn(lean_object* v_p_6_, lean_object* v_nvs_7_, lean_object* v_ctx_8_, lean_object* v_r_9_){
_start:
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = lean_apply_1(v_p_6_, v_ctx_8_);
v___x_11_ = lean_unbox(v___x_10_);
if (v___x_11_ == 0)
{
lean_dec(v_nvs_7_);
return v_r_9_;
}
else
{
lean_object* v_status_12_; lean_object* v_reason_13_; lean_object* v_headers_14_; lean_object* v_body_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_23_; 
v_status_12_ = lean_ctor_get(v_r_9_, 0);
v_reason_13_ = lean_ctor_get(v_r_9_, 1);
v_headers_14_ = lean_ctor_get(v_r_9_, 2);
v_body_15_ = lean_ctor_get(v_r_9_, 3);
v_isSharedCheck_23_ = !lean_is_exclusive(v_r_9_);
if (v_isSharedCheck_23_ == 0)
{
v___x_17_ = v_r_9_;
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_body_15_);
lean_inc(v_headers_14_);
lean_inc(v_reason_13_);
lean_inc(v_status_12_);
lean_dec(v_r_9_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_19_ = l_List_appendTR___redArg(v_headers_14_, v_nvs_7_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 2, v___x_19_);
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_status_12_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_reason_13_);
lean_ctor_set(v_reuseFailAlloc_22_, 2, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_22_, 3, v_body_15_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec___lam__0(lean_object* v_x_24_){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = 0;
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec___lam__0___boxed(lean_object* v_x_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec___lam__0(v_x_26_);
lean_dec_ref(v_x_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec(lean_object* v_p_30_, lean_object* v_nvs_31_){
_start:
{
lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___f_32_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec___closed__0));
v___x_33_ = lean_box(0);
v___x_34_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetProg(v_p_30_, v_nvs_31_);
v___x_35_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_35_, 0, v___f_32_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
lean_ctor_set(v___x_35_, 2, v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName___closed__1(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName___closed__0));
v___x_38_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName___closed__1);
return v___x_39_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal___closed__1(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal___closed__0));
v___x_42_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal___closed__1);
return v___x_43_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal___closed__1(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal___closed__0));
v___x_46_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal___closed__1);
return v___x_47_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName___closed__0));
v___x_50_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName___closed__1);
return v___x_51_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal___closed__0));
v___x_54_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal(void){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal___closed__1);
return v___x_55_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName___closed__1(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName___closed__0));
v___x_58_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName___closed__1);
return v___x_59_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName___closed__1(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName___closed__0));
v___x_62_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName(void){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName___closed__1);
return v___x_63_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName___closed__1(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName___closed__0));
v___x_66_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName___closed__1);
return v___x_67_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName___closed__1(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName___closed__0));
v___x_70_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName___closed__1);
return v___x_71_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName___closed__1(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName___closed__0));
v___x_74_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName___closed__1);
return v___x_75_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName___closed__1(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName___closed__0));
v___x_78_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName(void){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName___closed__1);
return v___x_79_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal___closed__1(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal___closed__0));
v___x_82_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal___closed__1);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_dashTypeSpec(lean_object* v_inScope_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName;
v___x_86_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal;
v___x_87_ = lp_orb_x2dcompiler_Pancake_StageLift2_stampSpec(v_inScope_84_, v___x_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_spaTypeSpec(lean_object* v_inScope_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName;
v___x_90_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal;
v___x_91_ = lp_orb_x2dcompiler_Pancake_StageLift2_stampSpec(v_inScope_88_, v___x_89_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseHeadSpec(lean_object* v_inScope_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName;
v___x_94_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal;
v___x_95_ = lp_orb_x2dcompiler_Pancake_StageLift2_stampSpec(v_inScope_92_, v___x_93_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieSpec(lean_object* v_inScope_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName;
v___x_98_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal;
v___x_99_ = lp_orb_x2dcompiler_Pancake_StageLift2_stampSpec(v_inScope_96_, v___x_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec___lam__0(lean_object* v_x_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = 1;
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec___lam__0___boxed(lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec___lam__0(v_x_102_);
lean_dec_ref(v_x_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec(lean_object* v_val_106_){
_start:
{
lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___f_107_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec___closed__0));
v___x_108_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName;
v___x_109_ = lp_orb_x2dcompiler_Pancake_StageLift2_stampSpec(v___f_107_, v___x_108_, v_val_106_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_proxyProtoSpec(lean_object* v_present_110_, lean_object* v_val_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName;
v___x_113_ = lp_orb_x2dcompiler_Pancake_StageLift2_stampSpec(v_present_110_, v___x_112_, v_val_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_corsSpec(lean_object* v_admits_114_, lean_object* v_val_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName;
v___x_117_ = lp_orb_x2dcompiler_Pancake_StageLift2_stampSpec(v_admits_114_, v___x_116_, v_val_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateSpec(lean_object* v_now_118_){
_start:
{
lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___f_119_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridSpec___closed__0));
v___x_120_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName;
v___x_121_ = lp_orb_x2dcompiler_Pancake_StageLift2_stampSpec(v___f_119_, v___x_120_, v_now_118_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_securityHeadersSpec(lean_object* v_wireHeaders_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lp_orb_x2dcompiler_Pancake_StageLift2_stampSetSpec(v_wireHeaders_122_);
return v___x_123_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__0(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal;
v___x_125_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName;
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__1(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_box(0);
v___x_128_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__0, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__0);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec(lean_object* v_inScope_130_, lean_object* v_tag_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_132_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName;
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v_tag_131_);
v___x_134_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_langStampSpec___closed__1);
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_condSetSpec(v_inScope_130_, v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__1(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__0));
v___x_139_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__3(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__2));
v___x_142_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__4(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__3);
v___x_144_ = lean_box(0);
v___x_145_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__1);
v___x_146_ = lean_unsigned_to_nat(413u);
v___x_147_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
lean_ctor_set(v___x_147_, 2, v___x_144_);
lean_ctor_set(v___x_147_, 3, v___x_143_);
return v___x_147_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge___closed__4);
return v___x_148_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__1(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__0));
v___x_151_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__3(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__2));
v___x_154_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__4(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_155_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__3);
v___x_156_ = lean_box(0);
v___x_157_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__1);
v___x_158_ = lean_unsigned_to_nat(503u);
v___x_159_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_156_);
lean_ctor_set(v___x_159_, 3, v___x_155_);
return v___x_159_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503___closed__4);
return v___x_160_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__1(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__0));
v___x_163_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__3(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__2));
v___x_166_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__4(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_167_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__3);
v___x_168_ = lean_box(0);
v___x_169_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__1);
v___x_170_ = lean_unsigned_to_nat(431u);
v___x_171_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
lean_ctor_set(v___x_171_, 3, v___x_167_);
return v___x_171_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge___closed__4);
return v___x_172_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__1(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__0));
v___x_175_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__3(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__2));
v___x_178_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__4(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_179_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__3);
v___x_180_ = lean_box(0);
v___x_181_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__1);
v___x_182_ = lean_unsigned_to_nat(414u);
v___x_183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
lean_ctor_set(v___x_183_, 2, v___x_180_);
lean_ctor_set(v___x_183_, 3, v___x_179_);
return v___x_183_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong(void){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong___closed__4);
return v___x_184_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__1(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__0));
v___x_187_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__3(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__2));
v___x_190_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__4(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_191_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__3);
v___x_192_ = lean_box(0);
v___x_193_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__1);
v___x_194_ = lean_unsigned_to_nat(429u);
v___x_195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 2, v___x_192_);
lean_ctor_set(v___x_195_, 3, v___x_191_);
return v___x_195_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429(void){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__4);
return v___x_196_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__1(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__0));
v___x_199_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__2(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_200_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__1);
v___x_201_ = lean_box(0);
v___x_202_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429___closed__1);
v___x_203_ = lean_unsigned_to_nat(429u);
v___x_204_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
lean_ctor_set(v___x_204_, 2, v___x_201_);
lean_ctor_set(v___x_204_, 3, v___x_200_);
return v___x_204_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__2, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429___closed__2);
return v___x_205_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__1(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__0));
v___x_208_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__3(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__2));
v___x_211_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__4(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_212_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__3);
v___x_213_ = lean_box(0);
v___x_214_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__1);
v___x_215_ = lean_unsigned_to_nat(408u);
v___x_216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
lean_ctor_set(v___x_216_, 2, v___x_213_);
lean_ctor_set(v___x_216_, 3, v___x_212_);
return v___x_216_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408___closed__4);
return v___x_217_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__0));
v___x_220_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__3(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__2));
v___x_223_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__5(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__4));
v___x_226_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__6(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__5, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__5);
v___x_228_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__3);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__7(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_box(0);
v___x_231_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__6, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__6);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__8(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_233_ = lean_box(0);
v___x_234_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__7, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__7);
v___x_235_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__1);
v___x_236_ = lean_unsigned_to_nat(304u);
v___x_237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_235_);
lean_ctor_set(v___x_237_, 2, v___x_234_);
lean_ctor_set(v___x_237_, 3, v___x_233_);
return v___x_237_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__8, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304___closed__8);
return v___x_238_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__1(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__0));
v___x_241_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__3(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__2));
v___x_244_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__4(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_245_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__3);
v___x_246_ = lean_box(0);
v___x_247_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__1);
v___x_248_ = lean_unsigned_to_nat(400u);
v___x_249_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
lean_ctor_set(v___x_249_, 2, v___x_246_);
lean_ctor_set(v___x_249_, 3, v___x_245_);
return v___x_249_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400___closed__4);
return v___x_250_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__1(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__0));
v___x_253_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__3(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__2));
v___x_256_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__4(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_257_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__3);
v___x_258_ = lean_box(0);
v___x_259_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__1);
v___x_260_ = lean_unsigned_to_nat(417u);
v___x_261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
lean_ctor_set(v___x_261_, 2, v___x_258_);
lean_ctor_set(v___x_261_, 3, v___x_257_);
return v___x_261_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417(void){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417___closed__4);
return v___x_262_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__1(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__0));
v___x_265_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__3(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__2));
v___x_268_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__4(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_269_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__3);
v___x_270_ = lean_box(0);
v___x_271_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__1);
v___x_272_ = lean_unsigned_to_nat(501u);
v___x_273_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
lean_ctor_set(v___x_273_, 2, v___x_270_);
lean_ctor_set(v___x_273_, 3, v___x_269_);
return v___x_273_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501(void){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501___closed__4);
return v___x_274_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__1(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__0));
v___x_277_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__3(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__2));
v___x_280_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__4(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_281_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__3);
v___x_282_ = lean_box(0);
v___x_283_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__1);
v___x_284_ = lean_unsigned_to_nat(505u);
v___x_285_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
lean_ctor_set(v___x_285_, 2, v___x_282_);
lean_ctor_set(v___x_285_, 3, v___x_281_);
return v___x_285_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505___closed__4);
return v___x_286_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__1(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__0));
v___x_289_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__3(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__2));
v___x_292_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__4(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_293_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__3);
v___x_294_ = lean_box(0);
v___x_295_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__1);
v___x_296_ = lean_unsigned_to_nat(421u);
v___x_297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
lean_ctor_set(v___x_297_, 2, v___x_294_);
lean_ctor_set(v___x_297_, 3, v___x_293_);
return v___x_297_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421(void){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421___closed__4);
return v___x_298_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__0));
v___x_301_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__3(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__2));
v___x_304_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__5(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__4));
v___x_307_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__6(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__5, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__5);
v___x_309_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__3);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__7(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_box(0);
v___x_312_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__6, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__6);
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__9(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__8));
v___x_316_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__10(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_317_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__9, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__9);
v___x_318_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__7, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__7);
v___x_319_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1);
v___x_320_ = lean_unsigned_to_nat(401u);
v___x_321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
lean_ctor_set(v___x_321_, 2, v___x_318_);
lean_ctor_set(v___x_321_, 3, v___x_317_);
return v___x_321_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized(void){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__10, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__10);
return v___x_322_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized___closed__1(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized___closed__0));
v___x_325_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized(lean_object* v_www_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_327_ = lean_unsigned_to_nat(401u);
v___x_328_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1);
v___x_329_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__3);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v_www_326_);
v___x_331_ = lean_box(0);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_basicUnauthorized___closed__1);
v___x_334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_334_, 0, v___x_327_);
lean_ctor_set(v___x_334_, 1, v___x_328_);
lean_ctor_set(v___x_334_, 2, v___x_332_);
lean_ctor_set(v___x_334_, 3, v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__0));
v___x_337_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__2(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_338_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1);
v___x_339_ = lean_box(0);
v___x_340_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1);
v___x_341_ = lean_unsigned_to_nat(401u);
v___x_342_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
lean_ctor_set(v___x_342_, 2, v___x_339_);
lean_ctor_set(v___x_342_, 3, v___x_338_);
return v___x_342_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401(void){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__2, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__2);
return v___x_343_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__1(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__0));
v___x_346_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__2(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_347_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1);
v___x_348_ = lean_box(0);
v___x_349_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__1);
v___x_350_ = lean_unsigned_to_nat(403u);
v___x_351_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_349_);
lean_ctor_set(v___x_351_, 2, v___x_348_);
lean_ctor_set(v___x_351_, 3, v___x_347_);
return v___x_351_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403(void){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__2, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__2);
return v___x_352_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__1(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__0));
v___x_355_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__3(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__2));
v___x_358_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__4(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_359_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__3);
v___x_360_ = lean_box(0);
v___x_361_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__1);
v___x_362_ = lean_unsigned_to_nat(500u);
v___x_363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_360_);
lean_ctor_set(v___x_363_, 3, v___x_359_);
return v___x_363_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500(void){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__4);
return v___x_364_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardResp500(void){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500___closed__4);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardReasonOf(lean_object* v_x_366_){
_start:
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(401u);
v___x_368_ = lean_nat_dec_eq(v_x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
v___x_369_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403___closed__1);
return v___x_369_;
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized___closed__1);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardReasonOf___boxed(lean_object* v_x_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardReasonOf(v_x_371_);
lean_dec(v_x_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardDenyResp(lean_object* v_status_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_374_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardReasonOf(v_status_373_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401___closed__1);
v___x_377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_377_, 0, v_status_373_);
lean_ctor_set(v___x_377_, 1, v___x_374_);
lean_ctor_set(v___x_377_, 2, v___x_375_);
lean_ctor_set(v___x_377_, 3, v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__1(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__0));
v___x_380_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__3(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__2));
v___x_383_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__4(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__3, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__3);
v___x_385_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__1);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_384_);
return v___x_386_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__6(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__5));
v___x_389_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__8(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__7));
v___x_392_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__9(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__8, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__8);
v___x_394_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__6, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__6);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_393_);
return v___x_395_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__10(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_box(0);
v___x_397_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__9, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__9);
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__11(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__10, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__10);
v___x_400_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__4, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__4);
v___x_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy(void){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__11, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy___closed__11);
return v___x_402_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__2(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__1));
v___x_407_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope(lean_object* v_c_408_){
_start:
{
lean_object* v_req_409_; lean_object* v_method_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_req_409_ = lean_ctor_get(v_c_408_, 0);
lean_inc_ref(v_req_409_);
lean_dec_ref(v_c_408_);
v_method_410_ = lean_ctor_get(v_req_409_, 0);
lean_inc(v_method_410_);
lean_dec_ref(v_req_409_);
v___x_411_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__0));
v___x_412_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__2, &lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___closed__2);
v___x_413_ = l_instDecidableEqList___redArg(v___x_411_, v_method_410_, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope___boxed(lean_object* v_c_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoInScope(v_c_414_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_StageLift2(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_StageLift2Inst(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_StageLift2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_ctName);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_htmlVal);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_sseVal);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_setCookieName);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_sessionCookieVal);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_ridName);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_00xffName);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_acaoName);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_dateName);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_clHdrName);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_varyName);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_langVaryVal);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_contentTooLarge);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp503);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_requestHeaderFieldsTooLarge);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_uriTooLong);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_stickResp429);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_rateResp429);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_resp408);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_notModified304);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_badRequest400);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_expectationFailed417);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_notImplemented501);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_badVersion505);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_misdirected421);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_bearerUnauthorized);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp401);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp403);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_authResp500);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardResp500 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardResp500();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_forwardResp500);
lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy = _init_lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Inst_demoPolicy);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
