// Lean compiler output
// Module: Pancake.ServeSlice
// Imports: public import Init public meta import Init public import Pancake.ServeFragment public import Pancake.SerializeCompile
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
lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile;
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_ByteArray_toList(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
extern lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11;
extern lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName;
uint8_t l_BitVec_slt(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secProg;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__4;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "src"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "len"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__6_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeSlice_sb_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_sb(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_sb___boxed(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Strict-Transport-Security"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "max-age=63072000; includeSubDomains"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__4;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "X-Frame-Options"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__5_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__6;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "DENY"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__7_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__9;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "X-Content-Type-Options"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__10_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__11;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nosniff"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__12_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__15;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__16;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__17;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "OK"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hello\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp200;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Method Not Allowed"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Allow"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__3;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "GET, POST, HEAD, OPTIONS"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__4_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__7;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "method not allowed\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__8_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__10;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_miniServe(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refNatToDec(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refBuild(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refBuild___boxed(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refAllHeaders(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refRenderHeaders(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refSerializeWire(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refSerialize(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refSerialize___boxed(lean_object*);
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision(lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__0, &lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__0);
v___x_3_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secProg(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__1, &lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secProg___closed__1);
return v___x_4_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__2(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_unsigned_to_nat(4u);
v___x_9_ = lean_unsigned_to_nat(64u);
v___x_10_ = l_BitVec_ofNat(v___x_9_, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__3(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__2);
v___x_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__4(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; lean_object* v___x_16_; 
v___x_13_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__3, &lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__3);
v___x_14_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__1));
v___x_15_ = 0;
v___x_16_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_16_, 0, v___x_14_);
lean_ctor_set(v___x_16_, 1, v___x_13_);
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*2, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg(lean_object* v_src200_19_, lean_object* v_src405_20_, lean_object* v_resp200_21_, lean_object* v_resp405_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_23_ = lp_orb_x2dcompiler_Pancake_ServeSlice_secProg;
v___x_24_ = lean_unsigned_to_nat(64u);
v___x_25_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__4, &lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__4);
v___x_26_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__5));
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v_src200_19_);
v___x_28_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_26_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
v___x_29_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__6));
v___x_30_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(v_resp200_21_);
v___x_31_ = l_List_lengthTR___redArg(v___x_30_);
lean_dec(v___x_30_);
v___x_32_ = l_BitVec_ofNat(v___x_24_, v___x_31_);
lean_dec(v___x_31_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
v___x_34_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_29_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
v___x_35_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_28_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
v___x_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_36_, 0, v_src405_20_);
v___x_37_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_26_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
v___x_38_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(v_resp405_22_);
v___x_39_ = l_List_lengthTR___redArg(v___x_38_);
lean_dec(v___x_38_);
v___x_40_ = l_BitVec_ofNat(v___x_24_, v___x_39_);
lean_dec(v___x_39_);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
v___x_42_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_29_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_37_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_44_, 0, v___x_25_);
lean_ctor_set(v___x_44_, 1, v___x_35_);
lean_ctor_set(v___x_44_, 2, v___x_43_);
v___x_45_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile;
v___x_46_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_44_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
v___x_47_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_23_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___boxed(lean_object* v_src200_48_, lean_object* v_src405_49_, lean_object* v_resp200_50_, lean_object* v_resp405_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg(v_src200_48_, v_src405_49_, v_resp200_50_, v_resp405_51_);
lean_dec_ref(v_resp405_51_);
lean_dec_ref(v_resp200_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg(lean_object* v_base__out_53_, lean_object* v_src200_54_, lean_object* v_src405_55_, lean_object* v_resp200_56_, lean_object* v_resp405_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg(v_src200_54_, v_src405_55_, v_resp200_56_, v_resp405_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___boxed(lean_object* v_base__out_59_, lean_object* v_src200_60_, lean_object* v_src405_61_, lean_object* v_resp200_62_, lean_object* v_resp405_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg(v_base__out_59_, v_src200_60_, v_src405_61_, v_resp200_62_, v_resp405_63_);
lean_dec_ref(v_resp405_63_);
lean_dec_ref(v_resp200_62_);
lean_dec(v_base__out_59_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeSlice_sb_spec__0(lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
if (lean_obj_tag(v_a_65_) == 0)
{
lean_object* v___x_67_; 
v___x_67_ = l_List_reverse___redArg(v_a_66_);
return v___x_67_;
}
else
{
lean_object* v_head_68_; lean_object* v_tail_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_81_; 
v_head_68_ = lean_ctor_get(v_a_65_, 0);
v_tail_69_ = lean_ctor_get(v_a_65_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v_a_65_);
if (v_isSharedCheck_81_ == 0)
{
v___x_71_ = v_a_65_;
v_isShared_72_ = v_isSharedCheck_81_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_tail_69_);
lean_inc(v_head_68_);
lean_dec(v_a_65_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_81_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_73_ = lean_unsigned_to_nat(8u);
v___x_74_ = lean_unbox(v_head_68_);
lean_dec(v_head_68_);
v___x_75_ = lean_uint8_to_nat(v___x_74_);
v___x_76_ = l_BitVec_ofNat(v___x_73_, v___x_75_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v_a_66_);
lean_ctor_set(v___x_71_, 0, v___x_76_);
v___x_78_ = v___x_71_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v_a_66_);
v___x_78_ = v_reuseFailAlloc_80_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
v_a_65_ = v_tail_69_;
v_a_66_ = v___x_78_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_sb(lean_object* v_s_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = lean_string_to_utf8(v_s_82_);
v___x_84_ = l_ByteArray_toList(v___x_83_);
lean_dec_ref(v___x_83_);
v___x_85_ = lean_box(0);
v___x_86_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeSlice_sb_spec__0(v___x_84_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_sb___boxed(lean_object* v_s_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v_s_87_);
lean_dec_ref(v_s_87_);
return v_res_88_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__1(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__0));
v___x_91_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__3(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__2));
v___x_94_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__4(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__3, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__3);
v___x_96_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__1, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__1);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__6(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__5));
v___x_100_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__8(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__7));
v___x_103_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__9(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__8, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__8);
v___x_105_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__6, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__6);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__11(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__10));
v___x_109_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__13(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__12));
v___x_112_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__14(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__13, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__13);
v___x_114_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__11, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__11);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
return v___x_115_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__15(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_box(0);
v___x_117_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__14, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__14);
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
return v___x_118_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__16(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__15, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__15);
v___x_120_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__9, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__9);
v___x_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
return v___x_121_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__17(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__16, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__16_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__16);
v___x_123_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__4, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__4);
v___x_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__17, &lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders___closed__17);
return v___x_125_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__1(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__0));
v___x_128_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__3(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__2));
v___x_131_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__4(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_132_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__3, &lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__3);
v___x_133_ = lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders;
v___x_134_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__1, &lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__1);
v___x_135_ = lean_unsigned_to_nat(200u);
v___x_136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_133_);
lean_ctor_set(v___x_136_, 3, v___x_132_);
return v___x_136_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp200(void){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__4, &lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp200___closed__4);
return v___x_137_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__1(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__0));
v___x_140_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__3(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__2));
v___x_143_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__5(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__4));
v___x_146_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__6(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__5, &lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__5);
v___x_148_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__3, &lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__3);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__7(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders;
v___x_151_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__6, &lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__6);
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__9(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__8));
v___x_155_ = lp_orb_x2dcompiler_Pancake_ServeSlice_sb(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__10(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__9, &lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__9);
v___x_157_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__7, &lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__7);
v___x_158_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__1, &lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__1);
v___x_159_ = lean_unsigned_to_nat(405u);
v___x_160_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
lean_ctor_set(v___x_160_, 2, v___x_157_);
lean_ctor_set(v___x_160_, 3, v___x_156_);
return v___x_160_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__10, &lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405___closed__10);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_miniServe(lean_object* v_tag_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = lean_unsigned_to_nat(64u);
v___x_164_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_serveSliceProg___redArg___closed__2);
v___x_165_ = l_BitVec_slt(v___x_163_, v_tag_162_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lp_orb_x2dcompiler_Pancake_ServeSlice_resp405;
return v___x_166_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = lp_orb_x2dcompiler_Pancake_ServeSlice_resp200;
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refNatToDec(lean_object* v_n_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_169_ = l_Nat_reprFast(v_n_168_);
v___x_170_ = lean_string_to_utf8(v___x_169_);
lean_dec_ref(v___x_169_);
v___x_171_ = l_ByteArray_toList(v___x_170_);
lean_dec_ref(v___x_170_);
v___x_172_ = lean_box(0);
v___x_173_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeSlice_sb_spec__0(v___x_171_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refBuild(lean_object* v_resp_174_){
_start:
{
lean_object* v_status_175_; lean_object* v_reason_176_; lean_object* v_headers_177_; lean_object* v_body_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_status_175_ = lean_ctor_get(v_resp_174_, 0);
v_reason_176_ = lean_ctor_get(v_resp_174_, 1);
v_headers_177_ = lean_ctor_get(v_resp_174_, 2);
v_body_178_ = lean_ctor_get(v_resp_174_, 3);
v___x_179_ = l_List_lengthTR___redArg(v_body_178_);
lean_inc(v_body_178_);
lean_inc(v_headers_177_);
lean_inc(v_reason_176_);
lean_inc(v_status_175_);
v___x_180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_180_, 0, v_status_175_);
lean_ctor_set(v___x_180_, 1, v_reason_176_);
lean_ctor_set(v___x_180_, 2, v_headers_177_);
lean_ctor_set(v___x_180_, 3, v___x_179_);
lean_ctor_set(v___x_180_, 4, v_body_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refBuild___boxed(lean_object* v_resp_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refBuild(v_resp_181_);
lean_dec_ref(v_resp_181_);
return v_res_182_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__0(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(32u);
v___x_184_ = lean_unsigned_to_nat(8u);
v___x_185_ = l_BitVec_ofNat(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_box(0);
v___x_187_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__0, &lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__0);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__2(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1, &lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1);
v___x_190_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_http11;
v___x_191_ = l_List_appendTR___redArg(v___x_190_, v___x_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine(lean_object* v_w_192_){
_start:
{
lean_object* v_status_193_; lean_object* v_reason_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_status_193_ = lean_ctor_get(v_w_192_, 0);
lean_inc(v_status_193_);
v_reason_194_ = lean_ctor_get(v_w_192_, 1);
lean_inc(v_reason_194_);
lean_dec_ref(v_w_192_);
v___x_195_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1, &lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1);
v___x_196_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__2, &lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__2);
v___x_197_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refNatToDec(v_status_193_);
v___x_198_ = l_List_appendTR___redArg(v___x_196_, v___x_197_);
v___x_199_ = l_List_appendTR___redArg(v___x_198_, v___x_195_);
v___x_200_ = l_List_appendTR___redArg(v___x_199_, v_reason_194_);
return v___x_200_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__0(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_unsigned_to_nat(58u);
v___x_202_ = lean_unsigned_to_nat(8u);
v___x_203_ = l_BitVec_ofNat(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__1(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1, &lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine___closed__1);
v___x_205_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__0, &lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__0);
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine(lean_object* v_nv_207_){
_start:
{
lean_object* v_fst_208_; lean_object* v_snd_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_fst_208_ = lean_ctor_get(v_nv_207_, 0);
lean_inc(v_fst_208_);
v_snd_209_ = lean_ctor_get(v_nv_207_, 1);
lean_inc(v_snd_209_);
lean_dec_ref(v_nv_207_);
v___x_210_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__1, &lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine___closed__1);
v___x_211_ = l_List_appendTR___redArg(v_fst_208_, v___x_210_);
v___x_212_ = l_List_appendTR___redArg(v___x_211_, v_snd_209_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refAllHeaders(lean_object* v_w_213_){
_start:
{
lean_object* v_headers_214_; lean_object* v_contentLength_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_headers_214_ = lean_ctor_get(v_w_213_, 2);
lean_inc(v_headers_214_);
v_contentLength_215_ = lean_ctor_get(v_w_213_, 3);
lean_inc(v_contentLength_215_);
lean_dec_ref(v_w_213_);
v___x_216_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_clName;
v___x_217_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refNatToDec(v_contentLength_215_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = l_List_appendTR___redArg(v_headers_214_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refRenderHeaders(lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(0);
return v___x_223_;
}
else
{
lean_object* v_tail_224_; 
v_tail_224_ = lean_ctor_get(v_x_222_, 1);
if (lean_obj_tag(v_tail_224_) == 0)
{
lean_object* v_head_225_; lean_object* v___x_226_; 
v_head_225_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_head_225_);
lean_dec_ref(v_x_222_);
v___x_226_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine(v_head_225_);
return v___x_226_;
}
else
{
lean_object* v_head_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
lean_inc(v_tail_224_);
v_head_227_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_head_227_);
lean_dec_ref(v_x_222_);
v___x_228_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refHeaderLine(v_head_227_);
v___x_229_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
v___x_230_ = l_List_appendTR___redArg(v___x_228_, v___x_229_);
v___x_231_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refRenderHeaders(v_tail_224_);
v___x_232_ = l_List_appendTR___redArg(v___x_230_, v___x_231_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refSerializeWire(lean_object* v_w_233_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_body_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_inc_ref(v_w_233_);
v___x_234_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refStatusLine(v_w_233_);
v___x_235_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
v___x_236_ = l_List_appendTR___redArg(v___x_234_, v___x_235_);
v_body_237_ = lean_ctor_get(v_w_233_, 4);
lean_inc(v_body_237_);
v___x_238_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refAllHeaders(v_w_233_);
v___x_239_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refRenderHeaders(v___x_238_);
v___x_240_ = l_List_appendTR___redArg(v___x_236_, v___x_239_);
v___x_241_ = l_List_appendTR___redArg(v___x_240_, v___x_235_);
v___x_242_ = l_List_appendTR___redArg(v___x_241_, v___x_235_);
v___x_243_ = l_List_appendTR___redArg(v___x_242_, v_body_237_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refSerialize(lean_object* v_resp_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refBuild(v_resp_244_);
v___x_246_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refSerializeWire(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_refSerialize___boxed(lean_object* v_resp_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = lp_orb_x2dcompiler_Pancake_ServeSlice_refSerialize(v_resp_247_);
lean_dec_ref(v_resp_247_);
return v_res_248_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_ServeFragment(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_SerializeCompile(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_ServeSlice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_ServeFragment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_SerializeCompile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_ServeSlice_secProg = _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secProg();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ServeSlice_secProg);
lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders = _init_lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ServeSlice_secHeaders);
lp_orb_x2dcompiler_Pancake_ServeSlice_resp200 = _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp200();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ServeSlice_resp200);
lp_orb_x2dcompiler_Pancake_ServeSlice_resp405 = _init_lp_orb_x2dcompiler_Pancake_ServeSlice_resp405();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ServeSlice_resp405);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
