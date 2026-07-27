// Lean compiler output
// Module: Pancake.ServeFragment
// Imports: public import Init public meta import Init public import Pancake.ProofProducing
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
uint8_t l_BitVec_slt(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "active"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__4;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__5_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision__translated___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision__translated(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision__translated___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__1;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "cldigits"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__3_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__4;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision__translated___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision__translated(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision__translated___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "octet"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__5;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision__translated___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision__translated(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision__translated___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision__translated___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision__translated(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision__translated___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hsts"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__2;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xfo"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__3_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__5;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nosniff"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__10;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_localVal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_localVal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__0(lean_object* v_activeVal_1_, lean_object* v___x_2_, lean_object* v___x_3_, lean_object* v_s_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_apply_1(v_activeVal_1_, v_s_4_);
v___x_6_ = l_BitVec_slt(v___x_2_, v___x_5_, v___x_3_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__0___boxed(lean_object* v_activeVal_7_, lean_object* v___x_8_, lean_object* v___x_9_, lean_object* v_s_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__0(v_activeVal_7_, v___x_8_, v___x_9_, v_s_10_);
lean_dec(v___x_8_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__1(lean_object* v___x_13_, lean_object* v_x_14_){
_start:
{
lean_inc(v___x_13_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__1___boxed(lean_object* v___x_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__1(v___x_15_, v_x_16_);
lean_dec_ref(v_x_16_);
lean_dec(v___x_15_);
return v_res_17_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_unsigned_to_nat(4u);
v___x_22_ = lean_unsigned_to_nat(64u);
v___x_23_ = l_BitVec_ofNat(v___x_22_, v___x_21_);
return v___x_23_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__3(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2);
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__4(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; lean_object* v___x_29_; 
v___x_26_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__3, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__3);
v___x_27_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__1));
v___x_28_ = 0;
v___x_29_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_29_, 0, v___x_27_);
lean_ctor_set(v___x_29_, 1, v___x_26_);
lean_ctor_set_uint8(v___x_29_, sizeof(void*)*2, v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__6(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_unsigned_to_nat(64u);
v___x_33_ = l_BitVec_ofNat(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7(void){
_start:
{
lean_object* v___x_34_; lean_object* v___f_35_; 
v___x_34_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__6, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__6);
v___f_35_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_35_, 0, v___x_34_);
return v___f_35_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__6, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__6);
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__9(void){
_start:
{
lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___f_38_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7);
v___x_39_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8);
v___x_40_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__5));
v___x_41_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_40_, v___x_39_, v___f_38_);
return v___x_41_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__9, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__9);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_unsigned_to_nat(64u);
v___x_46_ = l_BitVec_ofNat(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__12(void){
_start:
{
lean_object* v___x_47_; lean_object* v___f_48_; 
v___x_47_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11);
v___f_48_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_48_, 0, v___x_47_);
return v___f_48_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__13(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__14(void){
_start:
{
lean_object* v___f_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___f_51_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__12, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__12);
v___x_52_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__13, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__13);
v___x_53_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__5));
v___x_54_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_53_, v___x_52_, v___f_51_);
return v___x_54_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__14, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__14);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg(lean_object* v_activeVal_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___f_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_58_ = lean_unsigned_to_nat(64u);
v___x_59_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2);
v___f_60_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_60_, 0, v_activeVal_57_);
lean_closure_set(v___f_60_, 1, v___x_58_);
lean_closure_set(v___f_60_, 2, v___x_59_);
v___x_61_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__4, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__4);
v___x_62_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10);
v___x_63_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15);
v___x_64_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_64_, 0, v___x_61_);
lean_ctor_set(v___x_64_, 1, v___f_60_);
lean_ctor_set(v___x_64_, 2, v___x_62_);
lean_ctor_set(v___x_64_, 3, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision(lean_object* v_00_u03c3_65_, lean_object* v_activeVal_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg(v_activeVal_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision__translated___redArg(lean_object* v_activeVal_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg(v_activeVal_68_);
v___x_70_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision__translated(lean_object* v_00_u03c3_71_, lean_object* v_o_72_, lean_object* v_activeVal_73_, lean_object* v_hactive_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision__translated___redArg(v_activeVal_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision__translated___boxed(lean_object* v_00_u03c3_76_, lean_object* v_o_77_, lean_object* v_activeVal_78_, lean_object* v_hactive_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision__translated(v_00_u03c3_76_, v_o_77_, v_activeVal_78_, v_hactive_79_);
lean_dec_ref(v_o_77_);
return v_res_80_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___lam__0(lean_object* v_clVal_81_, lean_object* v___x_82_, lean_object* v___x_83_, lean_object* v_s_84_){
_start:
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = lean_apply_1(v_clVal_81_, v_s_84_);
v___x_86_ = l_BitVec_slt(v___x_82_, v___x_83_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___lam__0___boxed(lean_object* v_clVal_87_, lean_object* v___x_88_, lean_object* v___x_89_, lean_object* v_s_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___lam__0(v_clVal_87_, v___x_88_, v___x_89_, v_s_90_);
lean_dec(v___x_88_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__0(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_unsigned_to_nat(7u);
v___x_94_ = lean_unsigned_to_nat(64u);
v___x_95_ = l_BitVec_ofNat(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__1(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__0, &lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__0);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__4(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; 
v___x_101_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__3));
v___x_102_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__1, &lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__1);
v___x_103_ = 0;
v___x_104_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_101_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*2, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg(lean_object* v_clVal_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___f_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_106_ = lean_unsigned_to_nat(64u);
v___x_107_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__0, &lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__0);
v___f_108_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_108_, 0, v_clVal_105_);
lean_closure_set(v___f_108_, 1, v___x_106_);
lean_closure_set(v___f_108_, 2, v___x_107_);
v___x_109_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__4, &lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg___closed__4);
v___x_110_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10);
v___x_111_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15);
v___x_112_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_112_, 0, v___x_109_);
lean_ctor_set(v___x_112_, 1, v___f_108_);
lean_ctor_set(v___x_112_, 2, v___x_110_);
lean_ctor_set(v___x_112_, 3, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision(lean_object* v_00_u03c3_113_, lean_object* v_clVal_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg(v_clVal_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision__translated___redArg(lean_object* v_clVal_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision___redArg(v_clVal_116_);
v___x_118_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision__translated(lean_object* v_00_u03c3_119_, lean_object* v_o_120_, lean_object* v_clVal_121_, lean_object* v_hcl_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision__translated___redArg(v_clVal_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision__translated___boxed(lean_object* v_00_u03c3_124_, lean_object* v_o_125_, lean_object* v_clVal_126_, lean_object* v_hcl_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lp_orb_x2dcompiler_Pancake_ServeFragment_bodyLimitDecision__translated(v_00_u03c3_124_, v_o_125_, v_clVal_126_, v_hcl_127_);
lean_dec_ref(v_o_125_);
return v_res_128_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__0(lean_object* v_octetVal_129_, lean_object* v___x_130_, lean_object* v___x_131_, lean_object* v_s_132_){
_start:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = lean_apply_1(v_octetVal_129_, v_s_132_);
v___x_134_ = l_BitVec_slt(v___x_130_, v___x_133_, v___x_131_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__0___boxed(lean_object* v_octetVal_135_, lean_object* v___x_136_, lean_object* v___x_137_, lean_object* v_s_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__0(v_octetVal_135_, v___x_136_, v___x_137_, v_s_138_);
lean_dec(v___x_136_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__1(lean_object* v_octetVal_141_, lean_object* v___x_142_, lean_object* v___x_143_, lean_object* v_s_144_){
_start:
{
lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = lean_apply_1(v_octetVal_141_, v_s_144_);
v___x_146_ = l_BitVec_slt(v___x_142_, v___x_143_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__1___boxed(lean_object* v_octetVal_147_, lean_object* v___x_148_, lean_object* v___x_149_, lean_object* v_s_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__1(v_octetVal_147_, v___x_148_, v___x_149_, v_s_150_);
lean_dec(v___x_148_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__2(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_unsigned_to_nat(10u);
v___x_157_ = lean_unsigned_to_nat(64u);
v___x_158_ = l_BitVec_ofNat(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__3(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__2);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__4(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__3, &lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__3);
v___x_162_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__1));
v___x_163_ = 0;
v___x_164_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_161_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*2, v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__5(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; 
v___x_165_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__1));
v___x_166_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__3, &lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__3);
v___x_167_ = 0;
v___x_168_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_165_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*2, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg(lean_object* v_octetVal_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_170_ = lean_unsigned_to_nat(64u);
v___x_171_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__2);
lean_inc_ref(v_octetVal_169_);
v___f_172_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_172_, 0, v_octetVal_169_);
lean_closure_set(v___f_172_, 1, v___x_170_);
lean_closure_set(v___f_172_, 2, v___x_171_);
v___f_173_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_173_, 0, v_octetVal_169_);
lean_closure_set(v___f_173_, 1, v___x_170_);
lean_closure_set(v___f_173_, 2, v___x_171_);
v___x_174_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__4, &lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__4);
v___x_175_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10);
v___x_176_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__5, &lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg___closed__5);
v___x_177_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15);
v___x_178_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___f_173_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
lean_ctor_set(v___x_178_, 3, v___x_177_);
v___x_179_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_179_, 0, v___x_174_);
lean_ctor_set(v___x_179_, 1, v___f_172_);
lean_ctor_set(v___x_179_, 2, v___x_175_);
lean_ctor_set(v___x_179_, 3, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision(lean_object* v_00_u03c3_180_, lean_object* v_octetVal_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg(v_octetVal_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision__translated___redArg(lean_object* v_octetVal_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision___redArg(v_octetVal_183_);
v___x_185_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision__translated(lean_object* v_00_u03c3_186_, lean_object* v_o_187_, lean_object* v_octetVal_188_, lean_object* v_hoctet_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision__translated___redArg(v_octetVal_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision__translated___boxed(lean_object* v_00_u03c3_191_, lean_object* v_o_192_, lean_object* v_octetVal_193_, lean_object* v_hoctet_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = lp_orb_x2dcompiler_Pancake_ServeFragment_ipfilterDecision__translated(v_00_u03c3_191_, v_o_192_, v_octetVal_193_, v_hoctet_194_);
lean_dec_ref(v_o_192_);
return v_res_195_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___lam__0(lean_object* v_tagVal_196_, lean_object* v___x_197_, lean_object* v___x_198_, lean_object* v_s_199_){
_start:
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = lean_apply_1(v_tagVal_196_, v_s_199_);
v___x_201_ = l_BitVec_slt(v___x_197_, v___x_200_, v___x_198_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___lam__0___boxed(lean_object* v_tagVal_202_, lean_object* v___x_203_, lean_object* v___x_204_, lean_object* v_s_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___lam__0(v_tagVal_202_, v___x_203_, v___x_204_, v_s_205_);
lean_dec(v___x_203_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__2(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; 
v___x_211_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__3, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__3);
v___x_212_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__1));
v___x_213_ = 0;
v___x_214_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_211_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*2, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg(lean_object* v_tagVal_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_216_ = lean_unsigned_to_nat(64u);
v___x_217_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__2);
v___f_218_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_218_, 0, v_tagVal_215_);
lean_closure_set(v___f_218_, 1, v___x_216_);
lean_closure_set(v___f_218_, 2, v___x_217_);
v___x_219_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg___closed__2);
v___x_220_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__10);
v___x_221_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__15);
v___x_222_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_222_, 0, v___x_219_);
lean_ctor_set(v___x_222_, 1, v___f_218_);
lean_ctor_set(v___x_222_, 2, v___x_220_);
lean_ctor_set(v___x_222_, 3, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision(lean_object* v_00_u03c3_223_, lean_object* v_tagVal_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg(v_tagVal_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision__translated___redArg(lean_object* v_tagVal_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision___redArg(v_tagVal_226_);
v___x_228_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision__translated(lean_object* v_00_u03c3_229_, lean_object* v_o_230_, lean_object* v_tagVal_231_, lean_object* v_hmethod_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision__translated___redArg(v_tagVal_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision__translated___boxed(lean_object* v_00_u03c3_234_, lean_object* v_o_235_, lean_object* v_tagVal_236_, lean_object* v_hmethod_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = lp_orb_x2dcompiler_Pancake_ServeFragment_methodFilterDecision__translated(v_00_u03c3_234_, v_o_235_, v_tagVal_236_, v_hmethod_237_);
lean_dec_ref(v_o_235_);
return v_res_238_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__1(void){
_start:
{
lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___f_240_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7);
v___x_241_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8);
v___x_242_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__0));
v___x_243_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_242_, v___x_241_, v___f_240_);
return v___x_243_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__2(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__1, &lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__1);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__4(void){
_start:
{
lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___f_247_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7);
v___x_248_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8);
v___x_249_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__3));
v___x_250_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_249_, v___x_248_, v___f_247_);
return v___x_250_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__5(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__4, &lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__4);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__7(void){
_start:
{
lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___f_254_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__7);
v___x_255_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__8);
v___x_256_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__6));
v___x_257_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_256_, v___x_255_, v___f_254_);
return v___x_257_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__8(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__7, &lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__7);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__9(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__8, &lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__8);
v___x_261_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__5, &lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__5);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
return v___x_262_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__10(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__9, &lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__9);
v___x_264_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__2, &lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__2);
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision(lean_object* v_00_u03c3_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__10, &lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision___closed__10);
return v___x_267_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__0(void){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision(lean_box(0));
return v___x_268_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__1(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__0, &lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__0);
v___x_270_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated(lean_object* v_00_u03c3_271_, lean_object* v_o_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__1, &lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___closed__1);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated___boxed(lean_object* v_00_u03c3_274_, lean_object* v_o_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = lp_orb_x2dcompiler_Pancake_ServeFragment_securityHeadersDecision__translated(v_00_u03c3_274_, v_o_275_);
lean_dec_ref(v_o_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_localVal___redArg(lean_object* v_name_277_, lean_object* v_s_278_){
_start:
{
lean_object* v_locals_279_; lean_object* v___x_280_; 
v_locals_279_ = lean_ctor_get(v_s_278_, 0);
lean_inc_ref(v_locals_279_);
lean_dec_ref(v_s_278_);
v___x_280_ = lean_apply_1(v_locals_279_, v_name_277_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11, &lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_ServeFragment_connLimitDecision___redArg___closed__11);
return v___x_281_;
}
else
{
lean_object* v_val_282_; 
v_val_282_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_282_);
lean_dec_ref(v___x_280_);
return v_val_282_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeFragment_localVal(lean_object* v_00_u03c3_283_, lean_object* v_name_284_, lean_object* v_s_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lp_orb_x2dcompiler_Pancake_ServeFragment_localVal___redArg(v_name_284_, v_s_285_);
return v___x_286_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_ProofProducing(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_ServeFragment(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_ProofProducing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
