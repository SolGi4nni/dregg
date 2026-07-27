// Lean compiler output
// Module: Pancake.SerializeCompile
// Imports: public import Init public meta import Init public import Pancake.EmitCorrectClock
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_digitByte(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_digitByte___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_readFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_readFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_decAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_natToDec(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_build(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_build___boxed(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__13;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_http11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__15;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__16;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__17;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__18;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__19;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__20;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__21;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__22;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_clName;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_allHeaders(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_renderHeaders(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_serializeWire(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLineOf(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLineOf___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_headerBlockOf(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_headerBlockOf___boxed(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__10;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_wordOfByte(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_wordOfByte___boxed(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dst"};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__1_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__4_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "src"};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__6_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 7}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__7_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__4_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__9_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__14;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody;
static const lean_string_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "len"};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__3_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__3;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_digitByte(lean_object* v_d_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_2_ = lean_unsigned_to_nat(8u);
v___x_3_ = lean_unsigned_to_nat(48u);
v___x_4_ = lean_nat_add(v___x_3_, v_d_1_);
v___x_5_ = l_BitVec_ofNat(v___x_2_, v___x_4_);
lean_dec(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_digitByte___boxed(lean_object* v_d_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_digitByte(v_d_6_);
lean_dec(v_d_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_readFrom(lean_object* v_v_8_, lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
return v_v_8_;
}
else
{
lean_object* v_head_10_; lean_object* v_tail_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_head_10_ = lean_ctor_get(v_x_9_, 0);
v_tail_11_ = lean_ctor_get(v_x_9_, 1);
v___x_12_ = lean_unsigned_to_nat(10u);
v___x_13_ = lean_nat_mul(v_v_8_, v___x_12_);
lean_dec(v_v_8_);
v___x_14_ = lean_unsigned_to_nat(48u);
v___x_15_ = lean_nat_sub(v_head_10_, v___x_14_);
v___x_16_ = lean_nat_add(v___x_13_, v___x_15_);
lean_dec(v___x_15_);
lean_dec(v___x_13_);
v_v_8_ = v___x_16_;
v_x_9_ = v_tail_11_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_readFrom___boxed(lean_object* v_v_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_readFrom(v_v_18_, v_x_19_);
lean_dec(v_x_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_decAux(lean_object* v_x_21_, lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_zero_24_; uint8_t v_isZero_25_; 
v_zero_24_ = lean_unsigned_to_nat(0u);
v_isZero_25_ = lean_nat_dec_eq(v_x_21_, v_zero_24_);
if (v_isZero_25_ == 1)
{
lean_dec(v_x_22_);
lean_dec(v_x_21_);
return v_x_23_;
}
else
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(10u);
v___x_27_ = lean_nat_dec_lt(v_x_22_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v_one_28_; lean_object* v_n_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_one_28_ = lean_unsigned_to_nat(1u);
v_n_29_ = lean_nat_sub(v_x_21_, v_one_28_);
lean_dec(v_x_21_);
v___x_30_ = lean_nat_div(v_x_22_, v___x_26_);
v___x_31_ = lean_nat_mod(v_x_22_, v___x_26_);
lean_dec(v_x_22_);
v___x_32_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_digitByte(v___x_31_);
lean_dec(v___x_31_);
v___x_33_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v_x_23_);
v_x_21_ = v_n_29_;
v_x_22_ = v___x_30_;
v_x_23_ = v___x_33_;
goto _start;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec(v_x_21_);
v___x_35_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_digitByte(v_x_22_);
lean_dec(v_x_22_);
v___x_36_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v_x_23_);
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_natToDec(lean_object* v_n_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_add(v_n_37_, v___x_38_);
v___x_40_ = lean_box(0);
v___x_41_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_decAux(v___x_39_, v_n_37_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_build(lean_object* v_resp_42_){
_start:
{
lean_object* v_status_43_; lean_object* v_reason_44_; lean_object* v_headers_45_; lean_object* v_body_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_status_43_ = lean_ctor_get(v_resp_42_, 0);
v_reason_44_ = lean_ctor_get(v_resp_42_, 1);
v_headers_45_ = lean_ctor_get(v_resp_42_, 2);
v_body_46_ = lean_ctor_get(v_resp_42_, 3);
v___x_47_ = l_List_lengthTR___redArg(v_body_46_);
lean_inc(v_body_46_);
lean_inc(v_headers_45_);
lean_inc(v_reason_44_);
lean_inc(v_status_43_);
v___x_48_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_48_, 0, v_status_43_);
lean_ctor_set(v___x_48_, 1, v_reason_44_);
lean_ctor_set(v___x_48_, 2, v_headers_45_);
lean_ctor_set(v___x_48_, 3, v___x_47_);
lean_ctor_set(v___x_48_, 4, v_body_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_build___boxed(lean_object* v_resp_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_build(v_resp_49_);
lean_dec_ref(v_resp_49_);
return v_res_50_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__0(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_unsigned_to_nat(13u);
v___x_52_ = lean_unsigned_to_nat(8u);
v___x_53_ = l_BitVec_ofNat(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__1(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_unsigned_to_nat(10u);
v___x_55_ = lean_unsigned_to_nat(8u);
v___x_56_ = l_BitVec_ofNat(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__2(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_box(0);
v___x_58_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__1, &lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__1);
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__3(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__2, &lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__2);
v___x_61_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__0, &lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__0);
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf(void){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__3, &lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf___closed__3);
return v___x_63_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__0(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_unsigned_to_nat(72u);
v___x_65_ = lean_unsigned_to_nat(8u);
v___x_66_ = l_BitVec_ofNat(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__1(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_unsigned_to_nat(84u);
v___x_68_ = lean_unsigned_to_nat(8u);
v___x_69_ = l_BitVec_ofNat(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__2(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_unsigned_to_nat(80u);
v___x_71_ = lean_unsigned_to_nat(8u);
v___x_72_ = l_BitVec_ofNat(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__3(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_unsigned_to_nat(47u);
v___x_74_ = lean_unsigned_to_nat(8u);
v___x_75_ = l_BitVec_ofNat(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__4(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_unsigned_to_nat(49u);
v___x_77_ = lean_unsigned_to_nat(8u);
v___x_78_ = l_BitVec_ofNat(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__5(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(46u);
v___x_80_ = lean_unsigned_to_nat(8u);
v___x_81_ = l_BitVec_ofNat(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__6(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_box(0);
v___x_83_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__4, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__4);
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__7(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__6, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__6);
v___x_86_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__5, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__5);
v___x_87_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__8(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__7, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__7);
v___x_89_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__4, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__4);
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__9(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__8, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__8);
v___x_92_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__3, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__3);
v___x_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__10(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__9, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__9);
v___x_95_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__2, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__2);
v___x_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__11(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__10, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__10);
v___x_98_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__1, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__1);
v___x_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__12(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__11, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__11);
v___x_101_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__1, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__1);
v___x_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
return v___x_102_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__13(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__12, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__12);
v___x_104_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__0, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__0);
v___x_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11(void){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__13, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__13);
return v___x_106_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__0(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_unsigned_to_nat(67u);
v___x_108_ = lean_unsigned_to_nat(8u);
v___x_109_ = l_BitVec_ofNat(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__1(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_unsigned_to_nat(111u);
v___x_111_ = lean_unsigned_to_nat(8u);
v___x_112_ = l_BitVec_ofNat(v___x_111_, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_unsigned_to_nat(110u);
v___x_114_ = lean_unsigned_to_nat(8u);
v___x_115_ = l_BitVec_ofNat(v___x_114_, v___x_113_);
return v___x_115_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_unsigned_to_nat(116u);
v___x_117_ = lean_unsigned_to_nat(8u);
v___x_118_ = l_BitVec_ofNat(v___x_117_, v___x_116_);
return v___x_118_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__4(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_unsigned_to_nat(101u);
v___x_120_ = lean_unsigned_to_nat(8u);
v___x_121_ = l_BitVec_ofNat(v___x_120_, v___x_119_);
return v___x_121_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__5(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_unsigned_to_nat(45u);
v___x_123_ = lean_unsigned_to_nat(8u);
v___x_124_ = l_BitVec_ofNat(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__6(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_unsigned_to_nat(76u);
v___x_126_ = lean_unsigned_to_nat(8u);
v___x_127_ = l_BitVec_ofNat(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__7(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(103u);
v___x_129_ = lean_unsigned_to_nat(8u);
v___x_130_ = l_BitVec_ofNat(v___x_129_, v___x_128_);
return v___x_130_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__8(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_unsigned_to_nat(104u);
v___x_132_ = lean_unsigned_to_nat(8u);
v___x_133_ = l_BitVec_ofNat(v___x_132_, v___x_131_);
return v___x_133_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__9(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_box(0);
v___x_135_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__8, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__8);
v___x_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
return v___x_136_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__10(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__9, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__9);
v___x_138_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3);
v___x_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__11(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__10, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__10);
v___x_141_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__7, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__7);
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__12(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__11, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__11);
v___x_144_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2);
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__13(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__12, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__12);
v___x_147_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__4, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__4);
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
return v___x_148_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__14(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__13, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__13);
v___x_150_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__6, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__6);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__15(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__14, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__14);
v___x_153_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__5, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__5);
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__16(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__15, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__15);
v___x_156_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3);
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__17(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__16, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__16_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__16);
v___x_159_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2);
v___x_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__18(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__17, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__17);
v___x_162_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__4, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__4);
v___x_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__19(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__18, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__18_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__18);
v___x_165_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__3);
v___x_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__20(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__19, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__19_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__19);
v___x_168_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__2);
v___x_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__21(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__20, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__20_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__20);
v___x_171_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__1, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__1);
v___x_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__22(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__21, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__21_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__21);
v___x_174_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__0, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__0);
v___x_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
return v___x_175_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName(void){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__22, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__22_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__22);
return v___x_176_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__0(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_unsigned_to_nat(32u);
v___x_178_ = lean_unsigned_to_nat(8u);
v___x_179_ = l_BitVec_ofNat(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__0, &lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__0);
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__2(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1, &lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1);
v___x_184_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_http11;
v___x_185_ = l_List_appendTR___redArg(v___x_184_, v___x_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine(lean_object* v_w_186_){
_start:
{
lean_object* v_status_187_; lean_object* v_reason_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_status_187_ = lean_ctor_get(v_w_186_, 0);
lean_inc(v_status_187_);
v_reason_188_ = lean_ctor_get(v_w_186_, 1);
lean_inc(v_reason_188_);
lean_dec_ref(v_w_186_);
v___x_189_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1, &lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1);
v___x_190_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__2, &lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__2);
v___x_191_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_natToDec(v_status_187_);
v___x_192_ = l_List_appendTR___redArg(v___x_190_, v___x_191_);
v___x_193_ = l_List_appendTR___redArg(v___x_192_, v___x_189_);
v___x_194_ = l_List_appendTR___redArg(v___x_193_, v_reason_188_);
return v___x_194_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__0(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(58u);
v___x_196_ = lean_unsigned_to_nat(8u);
v___x_197_ = l_BitVec_ofNat(v___x_196_, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__1(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1, &lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine___closed__1);
v___x_199_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__0, &lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__0);
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine(lean_object* v_nv_201_){
_start:
{
lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_fst_202_ = lean_ctor_get(v_nv_201_, 0);
lean_inc(v_fst_202_);
v_snd_203_ = lean_ctor_get(v_nv_201_, 1);
lean_inc(v_snd_203_);
lean_dec_ref(v_nv_201_);
v___x_204_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__1, &lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine___closed__1);
v___x_205_ = l_List_appendTR___redArg(v_fst_202_, v___x_204_);
v___x_206_ = l_List_appendTR___redArg(v___x_205_, v_snd_203_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_allHeaders(lean_object* v_w_207_){
_start:
{
lean_object* v_headers_208_; lean_object* v_contentLength_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_headers_208_ = lean_ctor_get(v_w_207_, 2);
lean_inc(v_headers_208_);
v_contentLength_209_ = lean_ctor_get(v_w_207_, 3);
lean_inc(v_contentLength_209_);
lean_dec_ref(v_w_207_);
v___x_210_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_clName;
v___x_211_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_natToDec(v_contentLength_209_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = l_List_appendTR___redArg(v_headers_208_, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_renderHeaders(lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v_tail_218_; 
v_tail_218_ = lean_ctor_get(v_x_216_, 1);
if (lean_obj_tag(v_tail_218_) == 0)
{
lean_object* v_head_219_; lean_object* v___x_220_; 
v_head_219_ = lean_ctor_get(v_x_216_, 0);
lean_inc(v_head_219_);
lean_dec_ref(v_x_216_);
v___x_220_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine(v_head_219_);
return v___x_220_;
}
else
{
lean_object* v_head_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_inc(v_tail_218_);
v_head_221_ = lean_ctor_get(v_x_216_, 0);
lean_inc(v_head_221_);
lean_dec_ref(v_x_216_);
v___x_222_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_headerLine(v_head_221_);
v___x_223_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
v___x_224_ = l_List_appendTR___redArg(v___x_222_, v___x_223_);
v___x_225_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_renderHeaders(v_tail_218_);
v___x_226_ = l_List_appendTR___redArg(v___x_224_, v___x_225_);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_serializeWire(lean_object* v_w_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_body_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_inc_ref(v_w_227_);
v___x_228_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine(v_w_227_);
v___x_229_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf;
v___x_230_ = l_List_appendTR___redArg(v___x_228_, v___x_229_);
v_body_231_ = lean_ctor_get(v_w_227_, 4);
lean_inc(v_body_231_);
v___x_232_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_allHeaders(v_w_227_);
v___x_233_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_renderHeaders(v___x_232_);
v___x_234_ = l_List_appendTR___redArg(v___x_230_, v___x_233_);
v___x_235_ = l_List_appendTR___redArg(v___x_234_, v___x_229_);
v___x_236_ = l_List_appendTR___redArg(v___x_235_, v___x_229_);
v___x_237_ = l_List_appendTR___redArg(v___x_236_, v_body_231_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(lean_object* v_resp_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_build(v_resp_238_);
v___x_240_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_serializeWire(v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize___boxed(lean_object* v_resp_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(v_resp_241_);
lean_dec_ref(v_resp_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLineOf(lean_object* v_resp_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_build(v_resp_243_);
v___x_245_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLine(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLineOf___boxed(lean_object* v_resp_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_statusLineOf(v_resp_246_);
lean_dec_ref(v_resp_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_headerBlockOf(lean_object* v_resp_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_build(v_resp_248_);
v___x_250_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_allHeaders(v___x_249_);
v___x_251_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_renderHeaders(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_headerBlockOf___boxed(lean_object* v_resp_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_headerBlockOf(v_resp_252_);
lean_dec_ref(v_resp_252_);
return v_res_253_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__0(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(79u);
v___x_255_ = lean_unsigned_to_nat(8u);
v___x_256_ = l_BitVec_ofNat(v___x_255_, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__1(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_unsigned_to_nat(75u);
v___x_258_ = lean_unsigned_to_nat(8u);
v___x_259_ = l_BitVec_ofNat(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__2(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_box(0);
v___x_261_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__1, &lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__1);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
return v___x_262_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__3(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__2, &lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__2);
v___x_264_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__0, &lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__0);
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200(lean_object* v_body_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_267_ = lean_unsigned_to_nat(200u);
v___x_268_ = lean_box(0);
v___x_269_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__3, &lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__3);
v___x_270_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_270_, 0, v___x_267_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
lean_ctor_set(v___x_270_, 2, v___x_268_);
lean_ctor_set(v___x_270_, 3, v_body_266_);
return v___x_270_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__0(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_unsigned_to_nat(88u);
v___x_272_ = lean_unsigned_to_nat(8u);
v___x_273_ = l_BitVec_ofNat(v___x_272_, v___x_271_);
return v___x_273_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_unsigned_to_nat(65u);
v___x_275_ = lean_unsigned_to_nat(8u);
v___x_276_ = l_BitVec_ofNat(v___x_275_, v___x_274_);
return v___x_276_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__2(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_box(0);
v___x_278_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__1, &lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__1);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_277_);
return v___x_279_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__3(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__2, &lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__2);
v___x_281_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__5, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__5);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__4(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__3, &lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__3);
v___x_284_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__0, &lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__0);
v___x_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
return v___x_285_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__5(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__6, &lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11___closed__6);
v___x_287_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__4, &lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__4);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__6(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_box(0);
v___x_290_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__5, &lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__5);
v___x_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__7(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_unsigned_to_nat(105u);
v___x_293_ = lean_unsigned_to_nat(8u);
v___x_294_ = l_BitVec_ofNat(v___x_293_, v___x_292_);
return v___x_294_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__8(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_box(0);
v___x_296_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__7, &lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__7);
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__9(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__8, &lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__8);
v___x_299_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__8, &lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName___closed__8);
v___x_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__10(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_301_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__9, &lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__9);
v___x_302_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__6, &lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__6);
v___x_303_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__3, &lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_ok200___closed__3);
v___x_304_ = lean_unsigned_to_nat(200u);
v___x_305_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
lean_ctor_set(v___x_305_, 2, v___x_302_);
lean_ctor_set(v___x_305_, 3, v___x_301_);
return v___x_305_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp(void){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__10, &lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp___closed__10);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_wordOfByte(lean_object* v_b_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_unsigned_to_nat(8u);
v___x_309_ = lean_unsigned_to_nat(64u);
v___x_310_ = l_BitVec_setWidth(v___x_308_, v___x_309_, v_b_307_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_wordOfByte___boxed(lean_object* v_b_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_wordOfByte(v_b_311_);
lean_dec(v_b_311_);
return v_res_312_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__10(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_unsigned_to_nat(64u);
v___x_337_ = l_BitVec_ofNat(v___x_336_, v___x_335_);
return v___x_337_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__11(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__10, &lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__10);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__12(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; 
v___x_340_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__11, &lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__11);
v___x_341_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__3));
v___x_342_ = 0;
v___x_343_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_340_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*2, v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__13(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__12, &lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__12);
v___x_345_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__2));
v___x_346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__14(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__13, &lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__13);
v___x_348_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__9));
v___x_349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
return v___x_349_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody(void){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__14, &lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody___closed__14);
return v___x_350_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__3(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody;
v___x_359_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__2));
v___x_360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__3, &lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile___closed__3);
return v___x_361_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_EmitCorrectClock(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_SerializeCompile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_EmitCorrectClock(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf = _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_SerializeCompile_crlf);
lp_orb_x2dcompiler_Pancake_SerializeCompile_http11 = _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_http11();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_SerializeCompile_http11);
lp_orb_x2dcompiler_Pancake_SerializeCompile_clName = _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_clName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_SerializeCompile_clName);
lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp = _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_SerializeCompile_sampleResp);
lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody = _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_SerializeCompile_copyBody);
lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile = _init_lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_SerializeCompile_copyWhile);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
