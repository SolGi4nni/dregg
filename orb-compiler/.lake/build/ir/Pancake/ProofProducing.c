// Lean compiler output
// Module: Pancake.ProofProducing
// Imports: public import Init public meta import Init public import Pancake.EmitCorrectCompose public import Pancake.EmitCorrectClock
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
lean_object* lp_orb_x2dcompiler_Pancake_setLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_byteAlign(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_setByte(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
uint8_t l_BitVec_slt(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanFrom(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___lam__0___boxed(lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___closed__1_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storePrim___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storePrim___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storePrim___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storePrim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_putByteMem(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_putByteMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storeBytePrim___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storeBytePrim___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storeBytePrim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Pancake"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ProofProducing"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticWf_auto"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__3_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__3_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__2_value),LEAN_SCALAR_PTR_LITERAL(240, 167, 165, 57, 241, 161, 87, 44)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "wf_auto"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__3_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__6_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__6_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__4_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__4_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__4_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__4_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__7_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__7_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__7_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__7_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__9_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__9_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__9_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__9_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__11_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "repeat'"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__13_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__13_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__13_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(199, 67, 182, 138, 186, 187, 207, 59)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__13_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__14_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__15_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__15_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__15_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__15 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__15_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__16 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__16_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__17 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__17_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__18 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__18_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__19 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__19_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__20_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__20_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__20_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__20 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__20_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__21 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__21_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__22 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__22_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__23_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__23_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__23_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__23 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__23_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "wf_skip"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__24 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__24_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__25;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(184, 161, 233, 20, 156, 239, 142, 202)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__26 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__26_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__27_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__27_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(175, 207, 128, 87, 204, 218, 58, 8)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__27 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__27_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__28 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__28_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__29 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__29_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__30 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__30_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__31_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__31_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__31_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__31 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__31_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__32 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__32_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "refine"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__33 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__33_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__34_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__34_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__34_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(49, 130, 130, 160, 131, 48, 178, 245)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__34 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__34_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__35 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__35_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__36_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__36_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__36_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__36 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__36_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__37 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__37_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__38 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__38_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__39_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__39_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__39_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__39 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__39_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__40 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__40_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__41 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__41_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__42 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__42_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__43 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__43_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__44_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__44_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__44_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__44 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__44_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "wf_assign"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__45 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__45_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__46;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(114, 23, 189, 254, 129, 60, 227, 163)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__47 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__47_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__48_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__48_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(85, 215, 46, 176, 90, 207, 231, 202)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__48 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__48_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__49 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__49_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__49_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__50 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__50_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "wf_storeByte"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__51 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__51_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__52;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(67, 130, 156, 157, 174, 3, 58, 144)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__53 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__53_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__54_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__54_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(204, 107, 58, 221, 56, 188, 38, 134)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__54 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__54_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__55 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__55_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__55_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__56 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__56_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "wf_store"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__57 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__57_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__58;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(92, 212, 170, 228, 186, 102, 234, 178)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__59 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__59_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__60_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__60_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(19, 103, 13, 183, 201, 177, 210, 56)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__60 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__60_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__61 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__61_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__61_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__62 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__62_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__63 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__63_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__64 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__64_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__65 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__65_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__66_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__66_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__66_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__66 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__66_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "all_goals"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__67 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__67_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__68 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__68_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__69_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__69_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__69_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__68_value),LEAN_SCALAR_PTR_LITERAL(41, 145, 9, 18, 75, 146, 159, 78)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__69 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__69_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__70 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__70_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__71;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__72 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__72_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__73 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__73_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__74_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__74_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__74_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__73_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__74 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__74_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__75 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__75_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__76 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__76_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__77_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__77_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__77_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__77_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__77_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__77 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__77_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__78 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__78_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__79_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__79_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__79_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__78_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__79 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__79_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__80;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__81 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__81_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__82 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__82_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__83 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__83_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__84_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__84_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__84_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__83_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__84 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__84_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__85 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__85_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__86;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__85_value),LEAN_SCALAR_PTR_LITERAL(12, 151, 53, 232, 164, 85, 213, 132)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__87 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__87_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__88_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__85_value),LEAN_SCALAR_PTR_LITERAL(56, 7, 242, 173, 147, 120, 208, 251)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__88 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__88_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__88_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__89 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__89_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__88_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__90 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__90_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__90_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__91 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__91_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__90_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__91_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__92 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__92_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__89_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__92_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__93 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__93_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "signedLt"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__94 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__94_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__95;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__94_value),LEAN_SCALAR_PTR_LITERAL(173, 168, 23, 254, 170, 51, 75, 6)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__96 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__96_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__97_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__94_value),LEAN_SCALAR_PTR_LITERAL(129, 99, 228, 172, 90, 251, 123, 45)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__97 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__97_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__97_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__98 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__98_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__98_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__99 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__99_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "skipPrim"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__100 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__100_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__101;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__100_value),LEAN_SCALAR_PTR_LITERAL(41, 218, 125, 14, 232, 141, 210, 167)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__102 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__102_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__103_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__103_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__103_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__100_value),LEAN_SCALAR_PTR_LITERAL(70, 225, 50, 98, 164, 220, 197, 134)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__103 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__103_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__103_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__104 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__104_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__104_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__105 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__105_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assignPrim"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__106 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__106_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__107_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__107;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__106_value),LEAN_SCALAR_PTR_LITERAL(109, 53, 30, 139, 60, 182, 72, 230)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__108 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__108_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__109_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__109_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__109_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__109_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__106_value),LEAN_SCALAR_PTR_LITERAL(250, 107, 148, 167, 203, 59, 78, 167)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__109 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__109_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__109_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__110 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__110_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__110_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__111 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__111_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "storePrim"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__112 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__112_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__113_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__113;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__112_value),LEAN_SCALAR_PTR_LITERAL(192, 106, 199, 232, 114, 104, 88, 136)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__114 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__114_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__115_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__115_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__115_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__112_value),LEAN_SCALAR_PTR_LITERAL(7, 84, 48, 38, 117, 249, 227, 130)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__115 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__115_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__115_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__116 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__116_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__116_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__117 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__117_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "storeBytePrim"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__118 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__118_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__119_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__119;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__118_value),LEAN_SCALAR_PTR_LITERAL(119, 157, 232, 105, 118, 241, 230, 45)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__120 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__120_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__121_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__121_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__121_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__118_value),LEAN_SCALAR_PTR_LITERAL(240, 211, 26, 121, 204, 182, 137, 79)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__121 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__121_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__121_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__122 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__122_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__122_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__123 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__123_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.getD"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__124 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__124_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__125_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__125;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__126 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__126_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "getD"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__127 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__127_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__128_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__126_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__128_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__127_value),LEAN_SCALAR_PTR_LITERAL(129, 91, 222, 222, 88, 175, 46, 61)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__128 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__128_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__128_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__129 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__129_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__128_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__130 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__130_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__130_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__131 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__131_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__129_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__131_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__132 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__132_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__133 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__133_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__134 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__134_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__135_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__135_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__135_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__135_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__135_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__135 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__135_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__136 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__136_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__137_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__137_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__137_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__137_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__137_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__137_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__136_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__137 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__137_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__138 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__138_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__139_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__139_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__139_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__139_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__139_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__139_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__138_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__139 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__139_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "memaddrs_of_region"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__140 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__140_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__141_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__141;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__140_value),LEAN_SCALAR_PTR_LITERAL(127, 202, 61, 114, 247, 104, 36, 188)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__142 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__142_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__143_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__143_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__143_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__143_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__140_value),LEAN_SCALAR_PTR_LITERAL(72, 36, 239, 127, 111, 166, 124, 158)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__143 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__143_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__143_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__144 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__144_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__144_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__145 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__145_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__146 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__146_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__147 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__147_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__148_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__148_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__148_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__148_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__148_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__148_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__147_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__148 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__148_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__149 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__149_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__150_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__150_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__150_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__150_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__150_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__150_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__149_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__150 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__150_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpAll"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__151 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__151_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__152_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__152_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__152_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__152_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__152_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__152_value_aux_2),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__151_value),LEAN_SCALAR_PTR_LITERAL(5, 49, 55, 92, 153, 191, 153, 249)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__152 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__152_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simp_all"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__153 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__153_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_emitServe___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_emitServe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_translateCert___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_translateCert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_translateCert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__5;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__15;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__16;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__17;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__18 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__18_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__19;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__20;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__21;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__22;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__23;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__24;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo(lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__2;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__3_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__15;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__16;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__17;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__18;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__19;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__20;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__21;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__22;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__23;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__24;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__25;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__26;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__27;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__28;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__29;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage__translated___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage__translated(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage__translated___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_sampleCodeVal___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_sampleCodeVal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_line_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_line_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_line_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_frame_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_frame_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_frame_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_loop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_loop_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_loop_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_seqA_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_seqA_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_seqA_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_emitClk___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_emitClk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_emitClk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticWf_auto_clk_"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__1_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__1_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 236, 113, 11, 12, 33, 223, 130)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "wf_auto_clk "};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__3_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__5_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__9_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__10_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk__ = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__10_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "refinesClkOf"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__1;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 178, 209, 94, 235, 66, 111, 63)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 101, 223, 94, 91, 6, 245, 80)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__3_value_aux_0),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 49, 249, 187, 58, 229, 138, 217)}};
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__3_value_aux_1),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 187, 230, 40, 112, 67, 146, 181)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__3_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__4_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__7_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__1_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "len"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__2_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__1_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__4_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "acc"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__5_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__6_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ProofProducing_0__Pancake_EmitCorrectCompose_emit_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ProofProducing_0__Pancake_EmitCorrectCompose_emit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__6;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "buf"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp__translated___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp__translated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp__translated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_sampleBufVal___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_sampleBufVal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___lam__0(lean_object* v_s_1_){
_start:
{
lean_inc_ref(v_s_1_);
return v_s_1_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___lam__0___boxed(lean_object* v_s_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___lam__0(v_s_2_);
lean_dec_ref(v_s_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim(lean_object* v_00_u03c3_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim___closed__1));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg___lam__0(lean_object* v_f_10_, lean_object* v_x_11_, lean_object* v_s_12_){
_start:
{
lean_object* v_locals_13_; lean_object* v_memory_14_; lean_object* v_memaddrs_15_; uint8_t v_be_16_; lean_object* v_clock_17_; lean_object* v_ffi_18_; lean_object* v_baseAddr_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_locals_13_ = lean_ctor_get(v_s_12_, 0);
lean_inc_ref(v_locals_13_);
v_memory_14_ = lean_ctor_get(v_s_12_, 1);
lean_inc_ref(v_memory_14_);
v_memaddrs_15_ = lean_ctor_get(v_s_12_, 2);
lean_inc_ref(v_memaddrs_15_);
v_be_16_ = lean_ctor_get_uint8(v_s_12_, sizeof(void*)*6);
v_clock_17_ = lean_ctor_get(v_s_12_, 3);
lean_inc(v_clock_17_);
v_ffi_18_ = lean_ctor_get(v_s_12_, 4);
lean_inc(v_ffi_18_);
v_baseAddr_19_ = lean_ctor_get(v_s_12_, 5);
lean_inc(v_baseAddr_19_);
v___x_20_ = lean_apply_1(v_f_10_, v_s_12_);
v___x_21_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_setLocal___boxed), 4, 3);
lean_closure_set(v___x_21_, 0, v_locals_13_);
lean_closure_set(v___x_21_, 1, v_x_11_);
lean_closure_set(v___x_21_, 2, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_22_, 0, v___x_21_);
lean_ctor_set(v___x_22_, 1, v_memory_14_);
lean_ctor_set(v___x_22_, 2, v_memaddrs_15_);
lean_ctor_set(v___x_22_, 3, v_clock_17_);
lean_ctor_set(v___x_22_, 4, v_ffi_18_);
lean_ctor_set(v___x_22_, 5, v_baseAddr_19_);
lean_ctor_set_uint8(v___x_22_, sizeof(void*)*6, v_be_16_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(lean_object* v_x_23_, lean_object* v_e_24_, lean_object* v_f_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
lean_inc_ref(v_x_23_);
v___f_26_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg___lam__0), 3, 2);
lean_closure_set(v___f_26_, 0, v_f_25_);
lean_closure_set(v___f_26_, 1, v_x_23_);
v___x_27_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_27_, 0, v_x_23_);
lean_ctor_set(v___x_27_, 1, v_e_24_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v___f_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim(lean_object* v_00_u03c3_29_, lean_object* v_x_30_, lean_object* v_e_31_, lean_object* v_f_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v_x_30_, v_e_31_, v_f_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storePrim___redArg___lam__0(lean_object* v_addr_34_, lean_object* v_s_35_, lean_object* v_memory_36_, lean_object* v_val_37_, lean_object* v_k_38_){
_start:
{
lean_object* v___x_39_; uint8_t v___x_40_; 
lean_inc_ref(v_s_35_);
v___x_39_ = lean_apply_1(v_addr_34_, v_s_35_);
v___x_40_ = lean_nat_dec_eq(v_k_38_, v___x_39_);
lean_dec(v___x_39_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; 
lean_dec_ref(v_val_37_);
lean_dec_ref(v_s_35_);
v___x_41_ = lean_apply_1(v_memory_36_, v_k_38_);
return v___x_41_;
}
else
{
lean_object* v___x_42_; 
lean_dec(v_k_38_);
lean_dec_ref(v_memory_36_);
v___x_42_ = lean_apply_1(v_val_37_, v_s_35_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storePrim___redArg___lam__1(lean_object* v_addr_43_, lean_object* v_val_44_, lean_object* v_s_45_){
_start:
{
lean_object* v_locals_46_; lean_object* v_memory_47_; lean_object* v_memaddrs_48_; uint8_t v_be_49_; lean_object* v_clock_50_; lean_object* v_ffi_51_; lean_object* v_baseAddr_52_; lean_object* v___f_53_; lean_object* v___x_54_; 
v_locals_46_ = lean_ctor_get(v_s_45_, 0);
lean_inc_ref(v_locals_46_);
v_memory_47_ = lean_ctor_get(v_s_45_, 1);
lean_inc_ref(v_memory_47_);
v_memaddrs_48_ = lean_ctor_get(v_s_45_, 2);
lean_inc_ref(v_memaddrs_48_);
v_be_49_ = lean_ctor_get_uint8(v_s_45_, sizeof(void*)*6);
v_clock_50_ = lean_ctor_get(v_s_45_, 3);
lean_inc(v_clock_50_);
v_ffi_51_ = lean_ctor_get(v_s_45_, 4);
lean_inc(v_ffi_51_);
v_baseAddr_52_ = lean_ctor_get(v_s_45_, 5);
lean_inc(v_baseAddr_52_);
v___f_53_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_storePrim___redArg___lam__0), 5, 4);
lean_closure_set(v___f_53_, 0, v_addr_43_);
lean_closure_set(v___f_53_, 1, v_s_45_);
lean_closure_set(v___f_53_, 2, v_memory_47_);
lean_closure_set(v___f_53_, 3, v_val_44_);
v___x_54_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_54_, 0, v_locals_46_);
lean_ctor_set(v___x_54_, 1, v___f_53_);
lean_ctor_set(v___x_54_, 2, v_memaddrs_48_);
lean_ctor_set(v___x_54_, 3, v_clock_50_);
lean_ctor_set(v___x_54_, 4, v_ffi_51_);
lean_ctor_set(v___x_54_, 5, v_baseAddr_52_);
lean_ctor_set_uint8(v___x_54_, sizeof(void*)*6, v_be_49_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storePrim___redArg(lean_object* v_dst_55_, lean_object* v_src_56_, lean_object* v_addr_57_, lean_object* v_val_58_){
_start:
{
lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___f_59_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_storePrim___redArg___lam__1), 3, 2);
lean_closure_set(v___f_59_, 0, v_addr_57_);
lean_closure_set(v___f_59_, 1, v_val_58_);
v___x_60_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_60_, 0, v_dst_55_);
lean_ctor_set(v___x_60_, 1, v_src_56_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___f_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storePrim(lean_object* v_00_u03c3_62_, lean_object* v_dst_63_, lean_object* v_src_64_, lean_object* v_addr_65_, lean_object* v_val_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lp_orb_x2dcompiler_Pancake_ProofProducing_storePrim___redArg(v_dst_63_, v_src_64_, v_addr_65_, v_val_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_putByteMem(lean_object* v_m_68_, uint8_t v_be_69_, lean_object* v_adr_70_, lean_object* v_b_71_, lean_object* v_k_72_){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = lp_orb_x2dcompiler_Pancake_byteAlign(v_adr_70_);
v___x_74_ = lean_nat_dec_eq(v_k_72_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec(v___x_73_);
v___x_75_ = lean_apply_1(v_m_68_, v_k_72_);
return v___x_75_;
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v_k_72_);
v___x_76_ = lean_apply_1(v_m_68_, v___x_73_);
v___x_77_ = lp_orb_x2dcompiler_Pancake_setByte(v_adr_70_, v_b_71_, v___x_76_, v_be_69_);
lean_dec(v___x_76_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_putByteMem___boxed(lean_object* v_m_78_, lean_object* v_be_79_, lean_object* v_adr_80_, lean_object* v_b_81_, lean_object* v_k_82_){
_start:
{
uint8_t v_be_boxed_83_; lean_object* v_res_84_; 
v_be_boxed_83_ = lean_unbox(v_be_79_);
v_res_84_ = lp_orb_x2dcompiler_Pancake_ProofProducing_putByteMem(v_m_78_, v_be_boxed_83_, v_adr_80_, v_b_81_, v_k_82_);
lean_dec(v_b_81_);
lean_dec(v_adr_80_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storeBytePrim___redArg___lam__0(lean_object* v_adr_85_, lean_object* v_val_86_, lean_object* v_s_87_){
_start:
{
lean_object* v_locals_88_; lean_object* v_memory_89_; lean_object* v_memaddrs_90_; uint8_t v_be_91_; lean_object* v_clock_92_; lean_object* v_ffi_93_; lean_object* v_baseAddr_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_locals_88_ = lean_ctor_get(v_s_87_, 0);
lean_inc_ref(v_locals_88_);
v_memory_89_ = lean_ctor_get(v_s_87_, 1);
lean_inc_ref(v_memory_89_);
v_memaddrs_90_ = lean_ctor_get(v_s_87_, 2);
lean_inc_ref(v_memaddrs_90_);
v_be_91_ = lean_ctor_get_uint8(v_s_87_, sizeof(void*)*6);
v_clock_92_ = lean_ctor_get(v_s_87_, 3);
lean_inc(v_clock_92_);
v_ffi_93_ = lean_ctor_get(v_s_87_, 4);
lean_inc(v_ffi_93_);
v_baseAddr_94_ = lean_ctor_get(v_s_87_, 5);
lean_inc(v_baseAddr_94_);
lean_inc_ref(v_s_87_);
v___x_95_ = lean_apply_1(v_adr_85_, v_s_87_);
v___x_96_ = lean_unsigned_to_nat(64u);
v___x_97_ = lean_unsigned_to_nat(8u);
v___x_98_ = lean_apply_1(v_val_86_, v_s_87_);
v___x_99_ = l_BitVec_setWidth(v___x_96_, v___x_97_, v___x_98_);
lean_dec(v___x_98_);
v___x_100_ = lean_box(v_be_91_);
v___x_101_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_putByteMem___boxed), 5, 4);
lean_closure_set(v___x_101_, 0, v_memory_89_);
lean_closure_set(v___x_101_, 1, v___x_100_);
lean_closure_set(v___x_101_, 2, v___x_95_);
lean_closure_set(v___x_101_, 3, v___x_99_);
v___x_102_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_102_, 0, v_locals_88_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
lean_ctor_set(v___x_102_, 2, v_memaddrs_90_);
lean_ctor_set(v___x_102_, 3, v_clock_92_);
lean_ctor_set(v___x_102_, 4, v_ffi_93_);
lean_ctor_set(v___x_102_, 5, v_baseAddr_94_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*6, v_be_91_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storeBytePrim___redArg(lean_object* v_dst_103_, lean_object* v_src_104_, lean_object* v_adr_105_, lean_object* v_val_106_){
_start:
{
lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___f_107_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_storeBytePrim___redArg___lam__0), 3, 2);
lean_closure_set(v___f_107_, 0, v_adr_105_);
lean_closure_set(v___f_107_, 1, v_val_106_);
v___x_108_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_108_, 0, v_dst_103_);
lean_ctor_set(v___x_108_, 1, v_src_104_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___f_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_storeBytePrim(lean_object* v_00_u03c3_110_, lean_object* v_dst_111_, lean_object* v_src_112_, lean_object* v_adr_113_, lean_object* v_val_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lp_orb_x2dcompiler_Pancake_ProofProducing_storeBytePrim___redArg(v_dst_111_, v_src_112_, v_adr_113_, v_val_114_);
return v___x_115_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__25(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__24));
v___x_188_ = l_String_toRawSubstring_x27(v___x_187_);
return v___x_188_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__46(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__45));
v___x_238_ = l_String_toRawSubstring_x27(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__52(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__51));
v___x_253_ = l_String_toRawSubstring_x27(v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__58(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__57));
v___x_268_ = l_String_toRawSubstring_x27(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__71(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__70));
v___x_298_ = l_String_toRawSubstring_x27(v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__80(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Array_mkArray0(lean_box(0));
return v___x_320_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__86(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__85));
v___x_331_ = l_String_toRawSubstring_x27(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__95(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__94));
v___x_353_ = l_String_toRawSubstring_x27(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__101(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__100));
v___x_367_ = l_String_toRawSubstring_x27(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__107(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__106));
v___x_382_ = l_String_toRawSubstring_x27(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__113(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__112));
v___x_397_ = l_String_toRawSubstring_x27(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__119(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__118));
v___x_412_ = l_String_toRawSubstring_x27(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__125(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__124));
v___x_427_ = l_String_toRawSubstring_x27(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__141(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__140));
v___x_465_ = l_String_toRawSubstring_x27(v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1(lean_object* v_x_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto___closed__3));
v___x_502_ = l_Lean_Syntax_isOfKind(v_x_498_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_box(1);
v___x_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v_a_500_);
return v___x_504_;
}
else
{
lean_object* v_quotContext_505_; lean_object* v_currMacroScope_506_; lean_object* v_ref_507_; uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_quotContext_505_ = lean_ctor_get(v_a_499_, 1);
v_currMacroScope_506_ = lean_ctor_get(v_a_499_, 2);
v_ref_507_ = lean_ctor_get(v_a_499_, 5);
v___x_508_ = 0;
v___x_509_ = l_Lean_SourceInfo_fromRef(v_ref_507_, v___x_508_);
v___x_510_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__4));
v___x_511_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__5));
lean_inc_n(v___x_509_, 173);
v___x_512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_509_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__7));
v___x_514_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__9));
v___x_515_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__11));
v___x_516_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__12));
v___x_517_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__13));
v___x_518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_509_);
lean_ctor_set(v___x_518_, 1, v___x_516_);
v___x_519_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__14));
v___x_520_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__15));
v___x_521_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_509_);
lean_ctor_set(v___x_521_, 1, v___x_519_);
v___x_522_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__17));
v___x_523_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__18));
v___x_524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_509_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__19));
v___x_526_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__20));
v___x_527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_509_);
lean_ctor_set(v___x_527_, 1, v___x_525_);
v___x_528_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__23));
v___x_529_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__25, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__25_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__25);
v___x_530_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__26));
lean_inc_n(v_currMacroScope_506_, 13);
lean_inc_n(v_quotContext_505_, 13);
v___x_531_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_530_, v_currMacroScope_506_);
v___x_532_ = lean_box(0);
v___x_533_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__29));
v___x_534_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_534_, 0, v___x_509_);
lean_ctor_set(v___x_534_, 1, v___x_529_);
lean_ctor_set(v___x_534_, 2, v___x_531_);
lean_ctor_set(v___x_534_, 3, v___x_533_);
v___x_535_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__31));
v___x_536_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__32));
v___x_537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_509_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
lean_inc_ref(v___x_537_);
v___x_538_ = l_Lean_Syntax_node1(v___x_509_, v___x_535_, v___x_537_);
v___x_539_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_538_);
v___x_540_ = l_Lean_Syntax_node2(v___x_509_, v___x_528_, v___x_534_, v___x_539_);
v___x_541_ = l_Lean_Syntax_node2(v___x_509_, v___x_526_, v___x_527_, v___x_540_);
v___x_542_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_541_);
v___x_543_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_542_);
v___x_544_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_543_);
lean_inc_ref_n(v___x_524_, 12);
v___x_545_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_544_);
v___x_546_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__33));
v___x_547_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__34));
v___x_548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_509_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
v___x_549_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__36));
v___x_550_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__37));
v___x_551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_509_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__39));
v___x_553_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__40));
v___x_554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_509_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = l_Lean_Syntax_node2(v___x_509_, v___x_552_, v___x_554_, v___x_537_);
v___x_556_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__41));
v___x_557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_509_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
lean_inc_ref_n(v___x_557_, 9);
lean_inc_n(v___x_555_, 4);
v___x_558_ = l_Lean_Syntax_node5(v___x_509_, v___x_515_, v___x_555_, v___x_557_, v___x_555_, v___x_557_, v___x_555_);
v___x_559_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__42));
v___x_560_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_509_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
lean_inc_ref(v___x_560_);
lean_inc_ref(v___x_551_);
v___x_561_ = l_Lean_Syntax_node3(v___x_509_, v___x_549_, v___x_551_, v___x_558_, v___x_560_);
lean_inc_ref(v___x_548_);
v___x_562_ = l_Lean_Syntax_node2(v___x_509_, v___x_547_, v___x_548_, v___x_561_);
v___x_563_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_562_);
v___x_564_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_563_);
v___x_565_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_564_);
v___x_566_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_565_);
v___x_567_ = l_Lean_Syntax_node3(v___x_509_, v___x_515_, v___x_555_, v___x_557_, v___x_555_);
v___x_568_ = l_Lean_Syntax_node3(v___x_509_, v___x_549_, v___x_551_, v___x_567_, v___x_560_);
v___x_569_ = l_Lean_Syntax_node2(v___x_509_, v___x_547_, v___x_548_, v___x_568_);
v___x_570_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_569_);
v___x_571_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_570_);
v___x_572_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_571_);
v___x_573_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_572_);
v___x_574_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__43));
v___x_575_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__44));
v___x_576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_509_);
lean_ctor_set(v___x_576_, 1, v___x_574_);
v___x_577_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__46, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__46_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__46);
v___x_578_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__47));
v___x_579_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_578_, v_currMacroScope_506_);
v___x_580_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__50));
v___x_581_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_581_, 0, v___x_509_);
lean_ctor_set(v___x_581_, 1, v___x_577_);
lean_ctor_set(v___x_581_, 2, v___x_579_);
lean_ctor_set(v___x_581_, 3, v___x_580_);
lean_inc_ref_n(v___x_576_, 3);
v___x_582_ = l_Lean_Syntax_node2(v___x_509_, v___x_575_, v___x_576_, v___x_581_);
v___x_583_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_582_);
v___x_584_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_583_);
v___x_585_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_584_);
v___x_586_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_585_);
v___x_587_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__52, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__52_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__52);
v___x_588_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__53));
v___x_589_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_588_, v_currMacroScope_506_);
v___x_590_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__56));
v___x_591_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_591_, 0, v___x_509_);
lean_ctor_set(v___x_591_, 1, v___x_587_);
lean_ctor_set(v___x_591_, 2, v___x_589_);
lean_ctor_set(v___x_591_, 3, v___x_590_);
v___x_592_ = l_Lean_Syntax_node2(v___x_509_, v___x_575_, v___x_576_, v___x_591_);
v___x_593_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_592_);
v___x_594_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_593_);
v___x_595_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_594_);
v___x_596_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_595_);
v___x_597_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__58, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__58_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__58);
v___x_598_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__59));
v___x_599_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_598_, v_currMacroScope_506_);
v___x_600_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__62));
v___x_601_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_601_, 0, v___x_509_);
lean_ctor_set(v___x_601_, 1, v___x_597_);
lean_ctor_set(v___x_601_, 2, v___x_599_);
lean_ctor_set(v___x_601_, 3, v___x_600_);
v___x_602_ = l_Lean_Syntax_node2(v___x_509_, v___x_575_, v___x_576_, v___x_601_);
v___x_603_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_602_);
v___x_604_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_603_);
v___x_605_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_604_);
v___x_606_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_605_);
v___x_607_ = l_Lean_Syntax_node6(v___x_509_, v___x_515_, v___x_545_, v___x_566_, v___x_573_, v___x_586_, v___x_596_, v___x_606_);
lean_inc_ref_n(v___x_521_, 2);
v___x_608_ = l_Lean_Syntax_node2(v___x_509_, v___x_520_, v___x_521_, v___x_607_);
v___x_609_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_608_);
v___x_610_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_610_);
v___x_612_ = l_Lean_Syntax_node2(v___x_509_, v___x_517_, v___x_518_, v___x_611_);
v___x_613_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_612_);
v___x_614_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_613_);
v___x_615_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_614_);
v___x_616_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__63));
v___x_617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_509_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
lean_inc_ref_n(v___x_617_, 6);
lean_inc_ref_n(v___x_512_, 6);
v___x_618_ = l_Lean_Syntax_node3(v___x_509_, v___x_510_, v___x_512_, v___x_615_, v___x_617_);
v___x_619_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__64));
v___x_620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_509_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__66));
v___x_622_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__67));
v___x_623_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_509_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__68));
v___x_625_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__69));
v___x_626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_509_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
v___x_627_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__71, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__71_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__71);
v___x_628_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__72));
v___x_629_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_628_, v_currMacroScope_506_);
v___x_630_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_630_, 0, v___x_509_);
lean_ctor_set(v___x_630_, 1, v___x_627_);
lean_ctor_set(v___x_630_, 2, v___x_629_);
lean_ctor_set(v___x_630_, 3, v___x_532_);
v___x_631_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_630_);
v___x_632_ = l_Lean_Syntax_node2(v___x_509_, v___x_625_, v___x_626_, v___x_631_);
v___x_633_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__74));
v___x_634_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__75));
v___x_635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_509_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_Syntax_node1(v___x_509_, v___x_633_, v___x_635_);
v___x_637_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_636_);
v___x_638_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_637_);
v___x_639_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_638_);
v___x_640_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_639_);
v___x_641_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__76));
v___x_642_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__77));
v___x_643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_509_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
v___x_644_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__79));
v___x_645_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__80, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__80_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__80);
v___x_646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_646_, 0, v___x_509_);
lean_ctor_set(v___x_646_, 1, v___x_515_);
lean_ctor_set(v___x_646_, 2, v___x_645_);
lean_inc_ref_n(v___x_646_, 20);
v___x_647_ = l_Lean_Syntax_node1(v___x_509_, v___x_644_, v___x_646_);
v___x_648_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__81));
v___x_649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_509_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_649_);
v___x_651_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__82));
v___x_652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_509_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__84));
v___x_654_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__86, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__86_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__86);
v___x_655_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__87));
v___x_656_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_655_, v_currMacroScope_506_);
v___x_657_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__93));
v___x_658_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_658_, 0, v___x_509_);
lean_ctor_set(v___x_658_, 1, v___x_654_);
lean_ctor_set(v___x_658_, 2, v___x_656_);
lean_ctor_set(v___x_658_, 3, v___x_657_);
v___x_659_ = l_Lean_Syntax_node3(v___x_509_, v___x_653_, v___x_646_, v___x_646_, v___x_658_);
v___x_660_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__95, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__95_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__95);
v___x_661_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__96));
v___x_662_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_661_, v_currMacroScope_506_);
v___x_663_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__99));
v___x_664_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_664_, 0, v___x_509_);
lean_ctor_set(v___x_664_, 1, v___x_660_);
lean_ctor_set(v___x_664_, 2, v___x_662_);
lean_ctor_set(v___x_664_, 3, v___x_663_);
v___x_665_ = l_Lean_Syntax_node3(v___x_509_, v___x_653_, v___x_646_, v___x_646_, v___x_664_);
v___x_666_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__101, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__101_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__101);
v___x_667_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__102));
v___x_668_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_667_, v_currMacroScope_506_);
v___x_669_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__105));
v___x_670_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_670_, 0, v___x_509_);
lean_ctor_set(v___x_670_, 1, v___x_666_);
lean_ctor_set(v___x_670_, 2, v___x_668_);
lean_ctor_set(v___x_670_, 3, v___x_669_);
v___x_671_ = l_Lean_Syntax_node3(v___x_509_, v___x_653_, v___x_646_, v___x_646_, v___x_670_);
v___x_672_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__107, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__107_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__107);
v___x_673_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__108));
v___x_674_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_673_, v_currMacroScope_506_);
v___x_675_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__111));
v___x_676_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_676_, 0, v___x_509_);
lean_ctor_set(v___x_676_, 1, v___x_672_);
lean_ctor_set(v___x_676_, 2, v___x_674_);
lean_ctor_set(v___x_676_, 3, v___x_675_);
v___x_677_ = l_Lean_Syntax_node3(v___x_509_, v___x_653_, v___x_646_, v___x_646_, v___x_676_);
v___x_678_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__113, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__113_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__113);
v___x_679_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__114));
v___x_680_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_679_, v_currMacroScope_506_);
v___x_681_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__117));
v___x_682_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_682_, 0, v___x_509_);
lean_ctor_set(v___x_682_, 1, v___x_678_);
lean_ctor_set(v___x_682_, 2, v___x_680_);
lean_ctor_set(v___x_682_, 3, v___x_681_);
v___x_683_ = l_Lean_Syntax_node3(v___x_509_, v___x_653_, v___x_646_, v___x_646_, v___x_682_);
v___x_684_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__119, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__119_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__119);
v___x_685_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__120));
v___x_686_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_685_, v_currMacroScope_506_);
v___x_687_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__123));
v___x_688_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_688_, 0, v___x_509_);
lean_ctor_set(v___x_688_, 1, v___x_684_);
lean_ctor_set(v___x_688_, 2, v___x_686_);
lean_ctor_set(v___x_688_, 3, v___x_687_);
v___x_689_ = l_Lean_Syntax_node3(v___x_509_, v___x_653_, v___x_646_, v___x_646_, v___x_688_);
v___x_690_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__125, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__125_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__125);
v___x_691_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__128));
v___x_692_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_691_, v_currMacroScope_506_);
v___x_693_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__132));
v___x_694_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_694_, 0, v___x_509_);
lean_ctor_set(v___x_694_, 1, v___x_690_);
lean_ctor_set(v___x_694_, 2, v___x_692_);
lean_ctor_set(v___x_694_, 3, v___x_693_);
v___x_695_ = l_Lean_Syntax_node3(v___x_509_, v___x_653_, v___x_646_, v___x_646_, v___x_694_);
v___x_696_ = lean_unsigned_to_nat(13u);
v___x_697_ = lean_mk_empty_array_with_capacity(v___x_696_);
lean_inc(v___x_659_);
v___x_698_ = lean_array_push(v___x_697_, v___x_659_);
v___x_699_ = lean_array_push(v___x_698_, v___x_557_);
lean_inc(v___x_665_);
v___x_700_ = lean_array_push(v___x_699_, v___x_665_);
v___x_701_ = lean_array_push(v___x_700_, v___x_557_);
v___x_702_ = lean_array_push(v___x_701_, v___x_671_);
v___x_703_ = lean_array_push(v___x_702_, v___x_557_);
v___x_704_ = lean_array_push(v___x_703_, v___x_677_);
v___x_705_ = lean_array_push(v___x_704_, v___x_557_);
v___x_706_ = lean_array_push(v___x_705_, v___x_683_);
v___x_707_ = lean_array_push(v___x_706_, v___x_557_);
v___x_708_ = lean_array_push(v___x_707_, v___x_689_);
v___x_709_ = lean_array_push(v___x_708_, v___x_557_);
v___x_710_ = lean_array_push(v___x_709_, v___x_695_);
v___x_711_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_711_, 0, v___x_509_);
lean_ctor_set(v___x_711_, 1, v___x_515_);
lean_ctor_set(v___x_711_, 2, v___x_710_);
v___x_712_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__133));
v___x_713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_509_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
lean_inc_ref(v___x_713_);
lean_inc_ref(v___x_652_);
v___x_714_ = l_Lean_Syntax_node3(v___x_509_, v___x_515_, v___x_652_, v___x_711_, v___x_713_);
lean_inc(v___x_714_);
lean_inc(v___x_650_);
lean_inc_n(v___x_647_, 4);
lean_inc_ref(v___x_643_);
v___x_715_ = l_Lean_Syntax_node6(v___x_509_, v___x_642_, v___x_643_, v___x_647_, v___x_646_, v___x_650_, v___x_714_, v___x_646_);
v___x_716_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__134));
v___x_717_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__135));
v___x_718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_509_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
v___x_719_ = l_Lean_Syntax_node1(v___x_509_, v___x_717_, v___x_718_);
lean_inc_ref_n(v___x_620_, 3);
v___x_720_ = l_Lean_Syntax_node3(v___x_509_, v___x_515_, v___x_715_, v___x_620_, v___x_719_);
v___x_721_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_720_);
v___x_722_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_721_);
v___x_723_ = l_Lean_Syntax_node3(v___x_509_, v___x_510_, v___x_512_, v___x_722_, v___x_617_);
v___x_724_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_723_);
v___x_725_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_724_);
v___x_726_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_725_);
v___x_727_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_726_);
v___x_728_ = l_Lean_Syntax_node3(v___x_509_, v___x_515_, v___x_659_, v___x_557_, v___x_665_);
v___x_729_ = l_Lean_Syntax_node3(v___x_509_, v___x_515_, v___x_652_, v___x_728_, v___x_713_);
v___x_730_ = l_Lean_Syntax_node6(v___x_509_, v___x_642_, v___x_643_, v___x_647_, v___x_646_, v___x_650_, v___x_729_, v___x_646_);
v___x_731_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__136));
v___x_732_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__137));
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_509_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
v___x_734_ = l_Lean_Syntax_node2(v___x_509_, v___x_732_, v___x_733_, v___x_647_);
v___x_735_ = l_Lean_Syntax_node3(v___x_509_, v___x_515_, v___x_730_, v___x_620_, v___x_734_);
v___x_736_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_735_);
v___x_737_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_736_);
v___x_738_ = l_Lean_Syntax_node3(v___x_509_, v___x_510_, v___x_512_, v___x_737_, v___x_617_);
v___x_739_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_738_);
v___x_740_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_739_);
v___x_741_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_740_);
v___x_742_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_741_);
v___x_743_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__139));
v___x_744_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__141, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__141_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__141);
v___x_745_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__142));
v___x_746_ = l_Lean_addMacroScope(v_quotContext_505_, v___x_745_, v_currMacroScope_506_);
v___x_747_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__145));
v___x_748_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_748_, 0, v___x_509_);
lean_ctor_set(v___x_748_, 1, v___x_744_);
lean_ctor_set(v___x_748_, 2, v___x_746_);
lean_ctor_set(v___x_748_, 3, v___x_747_);
v___x_749_ = l_Lean_Syntax_node2(v___x_509_, v___x_575_, v___x_576_, v___x_748_);
v___x_750_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__146));
v___x_751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_509_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__147));
v___x_753_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__148));
v___x_754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_509_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
v___x_755_ = l_Lean_Syntax_node1(v___x_509_, v___x_753_, v___x_754_);
v___x_756_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_755_);
v___x_757_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_756_);
v___x_758_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_757_);
v___x_759_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_758_);
v___x_760_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__149));
v___x_761_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__150));
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_509_);
lean_ctor_set(v___x_762_, 1, v___x_760_);
v___x_763_ = l_Lean_Syntax_node2(v___x_509_, v___x_761_, v___x_762_, v___x_647_);
v___x_764_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_763_);
v___x_765_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_766_);
v___x_768_ = l_Lean_Syntax_node2(v___x_509_, v___x_515_, v___x_759_, v___x_767_);
v___x_769_ = l_Lean_Syntax_node2(v___x_509_, v___x_520_, v___x_521_, v___x_768_);
v___x_770_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_769_);
v___x_771_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_770_);
v___x_772_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_771_);
v___x_773_ = l_Lean_Syntax_node3(v___x_509_, v___x_510_, v___x_512_, v___x_772_, v___x_617_);
v___x_774_ = l_Lean_Syntax_node3(v___x_509_, v___x_743_, v___x_749_, v___x_751_, v___x_773_);
v___x_775_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_774_);
v___x_776_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node3(v___x_509_, v___x_510_, v___x_512_, v___x_777_, v___x_617_);
v___x_779_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_778_);
v___x_780_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_780_);
v___x_782_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_781_);
v___x_783_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__152));
v___x_784_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__153));
v___x_785_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_509_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_Syntax_node5(v___x_509_, v___x_783_, v___x_785_, v___x_647_, v___x_646_, v___x_646_, v___x_714_);
v___x_787_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_786_);
v___x_788_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_787_);
v___x_789_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_788_);
v___x_790_ = l_Lean_Syntax_node2(v___x_509_, v___x_522_, v___x_524_, v___x_789_);
v___x_791_ = l_Lean_Syntax_node5(v___x_509_, v___x_515_, v___x_640_, v___x_727_, v___x_742_, v___x_782_, v___x_790_);
v___x_792_ = l_Lean_Syntax_node2(v___x_509_, v___x_520_, v___x_521_, v___x_791_);
v___x_793_ = l_Lean_Syntax_node3(v___x_509_, v___x_515_, v___x_632_, v___x_620_, v___x_792_);
v___x_794_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_793_);
v___x_795_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_794_);
v___x_796_ = l_Lean_Syntax_node3(v___x_509_, v___x_510_, v___x_512_, v___x_795_, v___x_617_);
v___x_797_ = l_Lean_Syntax_node1(v___x_509_, v___x_515_, v___x_796_);
v___x_798_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_797_);
v___x_799_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_798_);
v___x_800_ = l_Lean_Syntax_node2(v___x_509_, v___x_621_, v___x_623_, v___x_799_);
v___x_801_ = l_Lean_Syntax_node3(v___x_509_, v___x_515_, v___x_618_, v___x_620_, v___x_800_);
v___x_802_ = l_Lean_Syntax_node1(v___x_509_, v___x_514_, v___x_801_);
v___x_803_ = l_Lean_Syntax_node1(v___x_509_, v___x_513_, v___x_802_);
v___x_804_ = l_Lean_Syntax_node3(v___x_509_, v___x_510_, v___x_512_, v___x_803_, v___x_617_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v_a_500_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___boxed(lean_object* v_x_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1(v_x_806_, v_a_807_, v_a_808_);
lean_dec_ref(v_a_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_emitServe___redArg(lean_object* v_a_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v_a_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_emitServe(lean_object* v_00_u03c3_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v_a_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_translateCert___redArg(lean_object* v_st_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v_st_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_translateCert(lean_object* v_00_u03c3_817_, lean_object* v_o_818_, lean_object* v_st_819_, lean_object* v_h_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v_st_819_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_translateCert___boxed(lean_object* v_00_u03c3_822_, lean_object* v_o_823_, lean_object* v_st_824_, lean_object* v_h_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = lp_orb_x2dcompiler_Pancake_ProofProducing_translateCert(v_00_u03c3_822_, v_o_823_, v_st_824_, v_h_825_);
lean_dec_ref(v_o_823_);
return v_res_826_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__0(lean_object* v_x_827_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = 1;
return v___x_828_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__0___boxed(lean_object* v_x_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__0(v_x_829_);
lean_dec_ref(v_x_829_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1(lean_object* v___x_832_, lean_object* v_x_833_){
_start:
{
lean_inc(v___x_832_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1___boxed(lean_object* v___x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1(v___x_834_, v_x_835_);
lean_dec_ref(v_x_835_);
lean_dec(v___x_834_);
return v_res_836_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_unsigned_to_nat(64u);
v___x_840_ = l_BitVec_ofNat(v___x_839_, v___x_838_);
return v___x_840_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__2(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__3(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_unsigned_to_nat(64u);
v___x_845_ = l_BitVec_ofNat(v___x_844_, v___x_843_);
return v___x_845_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__4(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__3, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__3);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__5(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; 
v___x_848_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__4, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__4);
v___x_849_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__2, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__2);
v___x_850_ = 0;
v___x_851_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_848_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*2, v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__7(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = lean_unsigned_to_nat(42u);
v___x_854_ = lean_unsigned_to_nat(64u);
v___x_855_ = l_BitVec_ofNat(v___x_854_, v___x_853_);
return v___x_855_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__8(void){
_start:
{
lean_object* v___x_856_; lean_object* v___f_857_; 
v___x_856_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__7, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__7);
v___f_857_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1___boxed), 2, 1);
lean_closure_set(v___f_857_, 0, v___x_856_);
return v___f_857_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__9(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__7, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__7);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__10(void){
_start:
{
lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___f_860_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__8, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__8);
v___x_861_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__9, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__9);
v___x_862_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__6));
v___x_863_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_862_, v___x_861_, v___f_860_);
return v___x_863_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__11(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__10, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__10);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__12(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_866_ = lean_unsigned_to_nat(99u);
v___x_867_ = lean_unsigned_to_nat(64u);
v___x_868_ = l_BitVec_ofNat(v___x_867_, v___x_866_);
return v___x_868_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__13(void){
_start:
{
lean_object* v___x_869_; lean_object* v___f_870_; 
v___x_869_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__12, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__12);
v___f_870_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1___boxed), 2, 1);
lean_closure_set(v___f_870_, 0, v___x_869_);
return v___f_870_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__14(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__12, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__12);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__15(void){
_start:
{
lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___f_873_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__13, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__13);
v___x_874_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__14, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__14);
v___x_875_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__6));
v___x_876_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_875_, v___x_874_, v___f_873_);
return v___x_876_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__16(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__15, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__15);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__17(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___f_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_879_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__16, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__16_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__16);
v___x_880_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__11, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__11);
v___f_881_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__0));
v___x_882_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__5, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__5);
v___x_883_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___f_881_);
lean_ctor_set(v___x_883_, 2, v___x_880_);
lean_ctor_set(v___x_883_, 3, v___x_879_);
return v___x_883_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__19(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_unsigned_to_nat(7u);
v___x_886_ = lean_unsigned_to_nat(64u);
v___x_887_ = l_BitVec_ofNat(v___x_886_, v___x_885_);
return v___x_887_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__20(void){
_start:
{
lean_object* v___x_888_; lean_object* v___f_889_; 
v___x_888_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__19, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__19_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__19);
v___f_889_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1___boxed), 2, 1);
lean_closure_set(v___f_889_, 0, v___x_888_);
return v___f_889_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__21(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__19, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__19_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__19);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__22(void){
_start:
{
lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___f_892_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__20, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__20_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__20);
v___x_893_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__21, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__21_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__21);
v___x_894_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__18));
v___x_895_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_894_, v___x_893_, v___f_892_);
return v___x_895_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__23(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__22, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__22_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__22);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__24(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__23, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__23_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__23);
v___x_899_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__17, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__17);
v___x_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo(lean_object* v_00_u03c3_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__24, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__24_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__24);
return v___x_902_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__0(void){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo(lean_box(0));
return v___x_903_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__1(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__0, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__0);
v___x_905_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated(lean_object* v_00_u03c3_906_, lean_object* v_o_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__1, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___closed__1);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated___boxed(lean_object* v_00_u03c3_909_, lean_object* v_o_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo__translated(v_00_u03c3_909_, v_o_910_);
lean_dec_ref(v_o_910_);
return v_res_911_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___lam__0(lean_object* v_codeVal_912_, lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v_s_915_){
_start:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_apply_1(v_codeVal_912_, v_s_915_);
v___x_917_ = l_BitVec_slt(v___x_913_, v___x_916_, v___x_914_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___lam__0___boxed(lean_object* v_codeVal_918_, lean_object* v___x_919_, lean_object* v___x_920_, lean_object* v_s_921_){
_start:
{
uint8_t v_res_922_; lean_object* v_r_923_; 
v_res_922_ = lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___lam__0(v_codeVal_918_, v___x_919_, v___x_920_, v_s_921_);
lean_dec(v___x_919_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__2(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; lean_object* v___x_930_; 
v___x_927_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__4, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__4);
v___x_928_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__1));
v___x_929_ = 0;
v___x_930_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_930_, 0, v___x_928_);
lean_ctor_set(v___x_930_, 1, v___x_927_);
lean_ctor_set_uint8(v___x_930_, sizeof(void*)*2, v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__4(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_unsigned_to_nat(301u);
v___x_933_ = lean_unsigned_to_nat(64u);
v___x_934_ = l_BitVec_ofNat(v___x_933_, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__5(void){
_start:
{
lean_object* v___x_935_; lean_object* v___f_936_; 
v___x_935_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__4, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__4);
v___f_936_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1___boxed), 2, 1);
lean_closure_set(v___f_936_, 0, v___x_935_);
return v___f_936_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__6(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__4, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__4);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
return v___x_938_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__7(void){
_start:
{
lean_object* v___f_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___f_939_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__5, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__5);
v___x_940_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__6, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__6);
v___x_941_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__3));
v___x_942_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_941_, v___x_940_, v___f_939_);
return v___x_942_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__8(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__7, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__7);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__9(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = lean_unsigned_to_nat(2u);
v___x_946_ = lean_unsigned_to_nat(64u);
v___x_947_ = l_BitVec_ofNat(v___x_946_, v___x_945_);
return v___x_947_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__10(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__9, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__9);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__11(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; 
v___x_950_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__10, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__10);
v___x_951_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__1));
v___x_952_ = 0;
v___x_953_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_950_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*2, v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__12(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = lean_unsigned_to_nat(302u);
v___x_955_ = lean_unsigned_to_nat(64u);
v___x_956_ = l_BitVec_ofNat(v___x_955_, v___x_954_);
return v___x_956_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__13(void){
_start:
{
lean_object* v___x_957_; lean_object* v___f_958_; 
v___x_957_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__12, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__12);
v___f_958_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1___boxed), 2, 1);
lean_closure_set(v___f_958_, 0, v___x_957_);
return v___f_958_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__14(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__12, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__12);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__15(void){
_start:
{
lean_object* v___f_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___f_961_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__13, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__13);
v___x_962_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__14, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__14);
v___x_963_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__3));
v___x_964_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_963_, v___x_962_, v___f_961_);
return v___x_964_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__16(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__15, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__15);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__17(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_unsigned_to_nat(3u);
v___x_968_ = lean_unsigned_to_nat(64u);
v___x_969_ = l_BitVec_ofNat(v___x_968_, v___x_967_);
return v___x_969_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__18(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__17, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__17);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__19(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; 
v___x_972_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__18, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__18_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__18);
v___x_973_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__1));
v___x_974_ = 0;
v___x_975_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_972_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*2, v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__20(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_unsigned_to_nat(307u);
v___x_977_ = lean_unsigned_to_nat(64u);
v___x_978_ = l_BitVec_ofNat(v___x_977_, v___x_976_);
return v___x_978_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__21(void){
_start:
{
lean_object* v___x_979_; lean_object* v___f_980_; 
v___x_979_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__20, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__20_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__20);
v___f_980_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1___boxed), 2, 1);
lean_closure_set(v___f_980_, 0, v___x_979_);
return v___f_980_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__22(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__20, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__20_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__20);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__23(void){
_start:
{
lean_object* v___f_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___f_983_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__21, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__21_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__21);
v___x_984_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__22, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__22_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__22);
v___x_985_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__3));
v___x_986_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_985_, v___x_984_, v___f_983_);
return v___x_986_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__24(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__23, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__23_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__23);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__25(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_unsigned_to_nat(308u);
v___x_990_ = lean_unsigned_to_nat(64u);
v___x_991_ = l_BitVec_ofNat(v___x_990_, v___x_989_);
return v___x_991_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__26(void){
_start:
{
lean_object* v___x_992_; lean_object* v___f_993_; 
v___x_992_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__25, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__25_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__25);
v___f_993_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___lam__1___boxed), 2, 1);
lean_closure_set(v___f_993_, 0, v___x_992_);
return v___f_993_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__27(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__25, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__25_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__25);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__28(void){
_start:
{
lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___f_996_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__26, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__26_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__26);
v___x_997_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__27, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__27_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__27);
v___x_998_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__3));
v___x_999_ = lp_orb_x2dcompiler_Pancake_ProofProducing_assignPrim___redArg(v___x_998_, v___x_997_, v___f_996_);
return v___x_999_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__29(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__28, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__28_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__28);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg(lean_object* v_codeVal_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1003_ = lean_unsigned_to_nat(64u);
v___x_1004_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__3, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__3);
lean_inc_ref_n(v_codeVal_1002_, 2);
v___f_1005_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1005_, 0, v_codeVal_1002_);
lean_closure_set(v___f_1005_, 1, v___x_1003_);
lean_closure_set(v___f_1005_, 2, v___x_1004_);
v___x_1006_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__2);
v___x_1007_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__8, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__8);
v___x_1008_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__9, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__9);
v___f_1009_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1009_, 0, v_codeVal_1002_);
lean_closure_set(v___f_1009_, 1, v___x_1003_);
lean_closure_set(v___f_1009_, 2, v___x_1008_);
v___x_1010_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__11, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__11);
v___x_1011_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__16, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__16_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__16);
v___x_1012_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__17, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__17);
v___f_1013_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1013_, 0, v_codeVal_1002_);
lean_closure_set(v___f_1013_, 1, v___x_1003_);
lean_closure_set(v___f_1013_, 2, v___x_1012_);
v___x_1014_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__19, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__19_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__19);
v___x_1015_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__24, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__24_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__24);
v___x_1016_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__29, &lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__29_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__29);
v___x_1017_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1014_);
lean_ctor_set(v___x_1017_, 1, v___f_1013_);
lean_ctor_set(v___x_1017_, 2, v___x_1015_);
lean_ctor_set(v___x_1017_, 3, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1010_);
lean_ctor_set(v___x_1018_, 1, v___f_1009_);
lean_ctor_set(v___x_1018_, 2, v___x_1011_);
lean_ctor_set(v___x_1018_, 3, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1006_);
lean_ctor_set(v___x_1019_, 1, v___f_1005_);
lean_ctor_set(v___x_1019_, 2, v___x_1007_);
lean_ctor_set(v___x_1019_, 3, v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage(lean_object* v_00_u03c3_1020_, lean_object* v_codeVal_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg(v_codeVal_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage__translated___redArg(lean_object* v_codeVal_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg(v_codeVal_1023_);
v___x_1025_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage__translated(lean_object* v_00_u03c3_1026_, lean_object* v_o_1027_, lean_object* v_codeVal_1028_, lean_object* v_hcode_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage__translated___redArg(v_codeVal_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage__translated___boxed(lean_object* v_00_u03c3_1031_, lean_object* v_o_1032_, lean_object* v_codeVal_1033_, lean_object* v_hcode_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage__translated(v_00_u03c3_1031_, v_o_1032_, v_codeVal_1033_, v_hcode_1034_);
lean_dec_ref(v_o_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_sampleCodeVal___redArg(lean_object* v_s_1036_){
_start:
{
lean_object* v_locals_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_locals_1037_ = lean_ctor_get(v_s_1036_, 0);
lean_inc_ref(v_locals_1037_);
lean_dec_ref(v_s_1036_);
v___x_1038_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__0));
v___x_1039_ = lean_apply_1(v_locals_1037_, v___x_1038_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1);
return v___x_1040_;
}
else
{
lean_object* v_val_1041_; 
v_val_1041_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_val_1041_);
lean_dec_ref(v___x_1039_);
return v_val_1041_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_sampleCodeVal(lean_object* v_00_u03c3_1042_, lean_object* v_s_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = lp_orb_x2dcompiler_Pancake_ProofProducing_sampleCodeVal___redArg(v_s_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorIdx___redArg(lean_object* v_x_1045_){
_start:
{
switch(lean_obj_tag(v_x_1045_))
{
case 0:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_unsigned_to_nat(0u);
return v___x_1046_;
}
case 1:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_unsigned_to_nat(1u);
return v___x_1047_;
}
case 2:
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_unsigned_to_nat(2u);
return v___x_1048_;
}
default: 
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_unsigned_to_nat(3u);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorIdx___redArg___boxed(lean_object* v_x_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorIdx___redArg(v_x_1050_);
lean_dec_ref(v_x_1050_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorIdx(lean_object* v_00_u03c3_1052_, lean_object* v_o_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_x_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorIdx___redArg(v_x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorIdx___boxed(lean_object* v_00_u03c3_1058_, lean_object* v_o_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorIdx(v_00_u03c3_1058_, v_o_1059_, v_a_1060_, v_a_1061_, v_x_1062_);
lean_dec_ref(v_x_1062_);
lean_dec_ref(v_o_1059_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___redArg(lean_object* v_t_1064_, lean_object* v_k_1065_){
_start:
{
switch(lean_obj_tag(v_t_1064_))
{
case 0:
{
lean_object* v_00_u03c6_1066_; lean_object* v_p_1067_; lean_object* v___x_1068_; 
v_00_u03c6_1066_ = lean_ctor_get(v_t_1064_, 0);
lean_inc_ref(v_00_u03c6_1066_);
v_p_1067_ = lean_ctor_get(v_t_1064_, 1);
lean_inc(v_p_1067_);
lean_dec_ref(v_t_1064_);
v___x_1068_ = lean_apply_3(v_k_1065_, v_00_u03c6_1066_, v_p_1067_, lean_box(0));
return v___x_1068_;
}
case 1:
{
lean_object* v_f_1069_; lean_object* v_x_1070_; lean_object* v_e_1071_; lean_object* v___x_1072_; 
v_f_1069_ = lean_ctor_get(v_t_1064_, 0);
lean_inc_ref(v_f_1069_);
v_x_1070_ = lean_ctor_get(v_t_1064_, 1);
lean_inc_ref(v_x_1070_);
v_e_1071_ = lean_ctor_get(v_t_1064_, 2);
lean_inc(v_e_1071_);
lean_dec_ref(v_t_1064_);
v___x_1072_ = lean_apply_5(v_k_1065_, lean_box(0), v_f_1069_, v_x_1070_, v_e_1071_, lean_box(0));
return v___x_1072_;
}
case 2:
{
lean_object* v_e_1073_; lean_object* v_body_1074_; lean_object* v_m_1075_; lean_object* v___x_1076_; 
v_e_1073_ = lean_ctor_get(v_t_1064_, 0);
lean_inc(v_e_1073_);
v_body_1074_ = lean_ctor_get(v_t_1064_, 1);
lean_inc(v_body_1074_);
v_m_1075_ = lean_ctor_get(v_t_1064_, 2);
lean_inc(v_m_1075_);
lean_dec_ref(v_t_1064_);
v___x_1076_ = lean_apply_6(v_k_1065_, lean_box(0), v_e_1073_, v_body_1074_, lean_box(0), lean_box(0), v_m_1075_);
return v___x_1076_;
}
default: 
{
lean_object* v_s1_1077_; lean_object* v_s2_1078_; lean_object* v___x_1079_; 
v_s1_1077_ = lean_ctor_get(v_t_1064_, 0);
lean_inc_ref(v_s1_1077_);
v_s2_1078_ = lean_ctor_get(v_t_1064_, 1);
lean_inc_ref(v_s2_1078_);
lean_dec_ref(v_t_1064_);
v___x_1079_ = lean_apply_7(v_k_1065_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_s1_1077_, v_s2_1078_, lean_box(0));
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim(lean_object* v_00_u03c3_1080_, lean_object* v_o_1081_, lean_object* v_motive_1082_, lean_object* v_ctorIdx_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_t_1086_, lean_object* v_h_1087_, lean_object* v_k_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___redArg(v_t_1086_, v_k_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___boxed(lean_object* v_00_u03c3_1090_, lean_object* v_o_1091_, lean_object* v_motive_1092_, lean_object* v_ctorIdx_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_t_1096_, lean_object* v_h_1097_, lean_object* v_k_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim(v_00_u03c3_1090_, v_o_1091_, v_motive_1092_, v_ctorIdx_1093_, v_a_1094_, v_a_1095_, v_t_1096_, v_h_1097_, v_k_1098_);
lean_dec(v_ctorIdx_1093_);
lean_dec_ref(v_o_1091_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_line_elim___redArg(lean_object* v_t_1100_, lean_object* v_line_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___redArg(v_t_1100_, v_line_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_line_elim(lean_object* v_00_u03c3_1103_, lean_object* v_o_1104_, lean_object* v_motive_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_t_1108_, lean_object* v_h_1109_, lean_object* v_line_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___redArg(v_t_1108_, v_line_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_line_elim___boxed(lean_object* v_00_u03c3_1112_, lean_object* v_o_1113_, lean_object* v_motive_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_t_1117_, lean_object* v_h_1118_, lean_object* v_line_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_line_elim(v_00_u03c3_1112_, v_o_1113_, v_motive_1114_, v_a_1115_, v_a_1116_, v_t_1117_, v_h_1118_, v_line_1119_);
lean_dec_ref(v_o_1113_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_frame_elim___redArg(lean_object* v_t_1121_, lean_object* v_frame_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___redArg(v_t_1121_, v_frame_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_frame_elim(lean_object* v_00_u03c3_1124_, lean_object* v_o_1125_, lean_object* v_motive_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_t_1129_, lean_object* v_h_1130_, lean_object* v_frame_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___redArg(v_t_1129_, v_frame_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_frame_elim___boxed(lean_object* v_00_u03c3_1133_, lean_object* v_o_1134_, lean_object* v_motive_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_t_1138_, lean_object* v_h_1139_, lean_object* v_frame_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_frame_elim(v_00_u03c3_1133_, v_o_1134_, v_motive_1135_, v_a_1136_, v_a_1137_, v_t_1138_, v_h_1139_, v_frame_1140_);
lean_dec_ref(v_o_1134_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_loop_elim___redArg(lean_object* v_t_1142_, lean_object* v_loop_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___redArg(v_t_1142_, v_loop_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_loop_elim(lean_object* v_00_u03c3_1145_, lean_object* v_o_1146_, lean_object* v_motive_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_t_1150_, lean_object* v_h_1151_, lean_object* v_loop_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___redArg(v_t_1150_, v_loop_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_loop_elim___boxed(lean_object* v_00_u03c3_1154_, lean_object* v_o_1155_, lean_object* v_motive_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_t_1159_, lean_object* v_h_1160_, lean_object* v_loop_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_loop_elim(v_00_u03c3_1154_, v_o_1155_, v_motive_1156_, v_a_1157_, v_a_1158_, v_t_1159_, v_h_1160_, v_loop_1161_);
lean_dec_ref(v_o_1155_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_seqA_elim___redArg(lean_object* v_t_1163_, lean_object* v_seqA_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___redArg(v_t_1163_, v_seqA_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_seqA_elim(lean_object* v_00_u03c3_1166_, lean_object* v_o_1167_, lean_object* v_motive_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_t_1171_, lean_object* v_h_1172_, lean_object* v_seqA_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_ctorElim___redArg(v_t_1171_, v_seqA_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_seqA_elim___boxed(lean_object* v_00_u03c3_1175_, lean_object* v_o_1176_, lean_object* v_motive_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_t_1180_, lean_object* v_h_1181_, lean_object* v_seqA_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = lp_orb_x2dcompiler_Pancake_ProofProducing_SClk_seqA_elim(v_00_u03c3_1175_, v_o_1176_, v_motive_1177_, v_a_1178_, v_a_1179_, v_t_1180_, v_h_1181_, v_seqA_1182_);
lean_dec_ref(v_o_1176_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_emitClk___redArg(lean_object* v_x_1184_){
_start:
{
switch(lean_obj_tag(v_x_1184_))
{
case 0:
{
lean_object* v_p_1185_; 
v_p_1185_ = lean_ctor_get(v_x_1184_, 1);
lean_inc(v_p_1185_);
lean_dec_ref(v_x_1184_);
return v_p_1185_;
}
case 1:
{
lean_object* v_x_1186_; lean_object* v_e_1187_; lean_object* v___x_1188_; 
v_x_1186_ = lean_ctor_get(v_x_1184_, 1);
lean_inc_ref(v_x_1186_);
v_e_1187_ = lean_ctor_get(v_x_1184_, 2);
lean_inc(v_e_1187_);
lean_dec_ref(v_x_1184_);
v___x_1188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1188_, 0, v_x_1186_);
lean_ctor_set(v___x_1188_, 1, v_e_1187_);
return v___x_1188_;
}
case 2:
{
lean_object* v_e_1189_; lean_object* v_body_1190_; lean_object* v___x_1191_; 
v_e_1189_ = lean_ctor_get(v_x_1184_, 0);
lean_inc(v_e_1189_);
v_body_1190_ = lean_ctor_get(v_x_1184_, 1);
lean_inc(v_body_1190_);
lean_dec_ref(v_x_1184_);
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v_e_1189_);
lean_ctor_set(v___x_1191_, 1, v_body_1190_);
return v___x_1191_;
}
default: 
{
lean_object* v_s1_1192_; lean_object* v_s2_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1202_; 
v_s1_1192_ = lean_ctor_get(v_x_1184_, 0);
v_s2_1193_ = lean_ctor_get(v_x_1184_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_x_1184_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1195_ = v_x_1184_;
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_s2_1193_);
lean_inc(v_s1_1192_);
lean_dec(v_x_1184_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1197_ = lp_orb_x2dcompiler_Pancake_ProofProducing_emitClk___redArg(v_s1_1192_);
v___x_1198_ = lp_orb_x2dcompiler_Pancake_ProofProducing_emitClk___redArg(v_s2_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set_tag(v___x_1195_, 5);
lean_ctor_set(v___x_1195_, 1, v___x_1198_);
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_emitClk(lean_object* v_00_u03c3_1203_, lean_object* v_o_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_, lean_object* v_x_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = lp_orb_x2dcompiler_Pancake_ProofProducing_emitClk___redArg(v_x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_emitClk___boxed(lean_object* v_00_u03c3_1209_, lean_object* v_o_1210_, lean_object* v_x_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = lp_orb_x2dcompiler_Pancake_ProofProducing_emitClk(v_00_u03c3_1209_, v_o_1210_, v_x_1211_, v_x_1212_, v_x_1213_);
lean_dec_ref(v_o_1210_);
return v_res_1214_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__1(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__0));
v___x_1244_ = l_String_toRawSubstring_x27(v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1(lean_object* v_x_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_tacticWf__auto__clk___00__closed__1));
lean_inc(v_x_1262_);
v___x_1266_ = l_Lean_Syntax_isOfKind(v_x_1262_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_dec(v_x_1262_);
v___x_1267_ = lean_box(1);
v___x_1268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
lean_ctor_set(v___x_1268_, 1, v_a_1264_);
return v___x_1268_;
}
else
{
lean_object* v_quotContext_1269_; lean_object* v_currMacroScope_1270_; lean_object* v_ref_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_quotContext_1269_ = lean_ctor_get(v_a_1263_, 1);
v_currMacroScope_1270_ = lean_ctor_get(v_a_1263_, 2);
v_ref_1271_ = lean_ctor_get(v_a_1263_, 5);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = l_Lean_Syntax_getArg(v_x_1262_, v___x_1272_);
lean_dec(v_x_1262_);
v___x_1274_ = 0;
v___x_1275_ = l_Lean_SourceInfo_fromRef(v_ref_1271_, v___x_1274_);
v___x_1276_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__19));
v___x_1277_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__20));
lean_inc_n(v___x_1275_, 4);
v___x_1278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1275_);
lean_ctor_set(v___x_1278_, 1, v___x_1276_);
v___x_1279_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__23));
v___x_1280_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__1, &lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__1);
v___x_1281_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__2));
lean_inc(v_currMacroScope_1270_);
lean_inc(v_quotContext_1269_);
v___x_1282_ = l_Lean_addMacroScope(v_quotContext_1269_, v___x_1281_, v_currMacroScope_1270_);
v___x_1283_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___closed__7));
v___x_1284_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1275_);
lean_ctor_set(v___x_1284_, 1, v___x_1280_);
lean_ctor_set(v___x_1284_, 2, v___x_1282_);
lean_ctor_set(v___x_1284_, 3, v___x_1283_);
v___x_1285_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__1___closed__11));
v___x_1286_ = l_Lean_Syntax_node1(v___x_1275_, v___x_1285_, v___x_1273_);
v___x_1287_ = l_Lean_Syntax_node2(v___x_1275_, v___x_1279_, v___x_1284_, v___x_1286_);
v___x_1288_ = l_Lean_Syntax_node2(v___x_1275_, v___x_1277_, v___x_1278_, v___x_1287_);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v_a_1264_);
return v___x_1289_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1___boxed(lean_object* v_x_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = lp_orb_x2dcompiler_Pancake_ProofProducing___aux__Pancake__ProofProducing______macroRules__Pancake__ProofProducing__tacticWf__auto__clk____1(v_x_1290_, v_a_1291_, v_a_1292_);
lean_dec_ref(v_a_1291_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___lam__0(lean_object* v_a_1294_, lean_object* v_off_1295_, lean_object* v_len_1296_, lean_object* v_x_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = lean_unsigned_to_nat(64u);
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = lp_orb_x2dcompiler_Pancake_EmitCorrect_scanFrom(v_a_1294_, v_off_1295_, v_len_1296_, v___x_1299_);
v___x_1301_ = l_BitVec_ofNat(v___x_1298_, v___x_1300_);
lean_dec(v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___lam__0___boxed(lean_object* v_a_1302_, lean_object* v_off_1303_, lean_object* v_len_1304_, lean_object* v_x_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___lam__0(v_a_1302_, v_off_1303_, v_len_1304_, v_x_1305_);
lean_dec_ref(v_x_1305_);
lean_dec(v_a_1302_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg(lean_object* v_a_1320_, lean_object* v_off_1321_, lean_object* v_len_1322_){
_start:
{
lean_object* v___f_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_inc(v_len_1322_);
v___f_1323_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1323_, 0, v_a_1320_);
lean_closure_set(v___f_1323_, 1, v_off_1321_);
lean_closure_set(v___f_1323_, 2, v_len_1322_);
v___x_1324_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__4));
v___x_1325_ = lp_orb_x2dcompiler_Pancake_EmitCorrect_scanBody;
v___x_1326_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
lean_ctor_set(v___x_1326_, 2, v_len_1322_);
v___x_1327_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_redirectStatusStage___redArg___closed__3));
v___x_1328_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg___closed__6));
v___x_1329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1329_, 0, v___f_1323_);
lean_ctor_set(v___x_1329_, 1, v___x_1327_);
lean_ctor_set(v___x_1329_, 2, v___x_1328_);
v___x_1330_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1326_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage(lean_object* v_00_u03c3_1331_, lean_object* v_o_1332_, lean_object* v_a_1333_, lean_object* v_buf_1334_, lean_object* v_off_1335_, lean_object* v_len_1336_, lean_object* v_hlen63_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___redArg(v_a_1333_, v_off_1335_, v_len_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage___boxed(lean_object* v_00_u03c3_1339_, lean_object* v_o_1340_, lean_object* v_a_1341_, lean_object* v_buf_1342_, lean_object* v_off_1343_, lean_object* v_len_1344_, lean_object* v_hlen63_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = lp_orb_x2dcompiler_Pancake_ProofProducing_scanPublishStage(v_00_u03c3_1339_, v_o_1340_, v_a_1341_, v_buf_1342_, v_off_1343_, v_len_1344_, v_hlen63_1345_);
lean_dec(v_buf_1342_);
lean_dec_ref(v_o_1340_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__0(lean_object* v_b_1347_, lean_object* v_x_1348_){
_start:
{
lean_inc(v_b_1347_);
return v_b_1347_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__0___boxed(lean_object* v_b_1349_, lean_object* v_x_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__0(v_b_1349_, v_x_1350_);
lean_dec_ref(v_x_1350_);
lean_dec(v_b_1349_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__1(lean_object* v_base_1352_, lean_object* v___x_1353_, lean_object* v___x_1354_, lean_object* v_s_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_apply_1(v_base_1352_, v_s_1355_);
v___x_1357_ = l_BitVec_add(v___x_1353_, v___x_1356_, v___x_1354_);
lean_dec(v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__1___boxed(lean_object* v_base_1358_, lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v_s_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__1(v_base_1358_, v___x_1359_, v___x_1360_, v_s_1361_);
lean_dec(v___x_1360_);
lean_dec(v___x_1359_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg(lean_object* v_base_1363_, lean_object* v_baseE_1364_, lean_object* v_off_1365_, lean_object* v_b_1366_){
_start:
{
lean_object* v___f_1367_; uint8_t v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___f_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_inc(v_b_1366_);
v___f_1367_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1367_, 0, v_b_1366_);
v___x_1368_ = 0;
v___x_1369_ = lean_unsigned_to_nat(64u);
v___x_1370_ = l_BitVec_ofNat(v___x_1369_, v_off_1365_);
lean_inc(v___x_1370_);
v___f_1371_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1371_, 0, v_base_1363_);
lean_closure_set(v___f_1371_, 1, v___x_1369_);
lean_closure_set(v___f_1371_, 2, v___x_1370_);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1370_);
v___x_1373_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_1373_, 0, v_baseE_1364_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*2, v___x_1368_);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_b_1366_);
v___x_1375_ = lp_orb_x2dcompiler_Pancake_ProofProducing_storeBytePrim___redArg(v___x_1373_, v___x_1374_, v___f_1371_, v___f_1367_);
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg___boxed(lean_object* v_base_1377_, lean_object* v_baseE_1378_, lean_object* v_off_1379_, lean_object* v_b_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg(v_base_1377_, v_baseE_1378_, v_off_1379_, v_b_1380_);
lean_dec(v_off_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf(lean_object* v_00_u03c3_1382_, lean_object* v_base_1383_, lean_object* v_baseE_1384_, lean_object* v_off_1385_, lean_object* v_b_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg(v_base_1383_, v_baseE_1384_, v_off_1385_, v_b_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___boxed(lean_object* v_00_u03c3_1388_, lean_object* v_base_1389_, lean_object* v_baseE_1390_, lean_object* v_off_1391_, lean_object* v_b_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf(v_00_u03c3_1388_, v_base_1389_, v_baseE_1390_, v_off_1391_, v_b_1392_);
lean_dec(v_off_1391_);
return v_res_1393_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__0(void){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = lp_orb_x2dcompiler_Pancake_ProofProducing_skipPrim(lean_box(0));
return v___x_1394_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__1(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__0, &lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__0);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg(lean_object* v_base_1397_, lean_object* v_baseE_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
if (lean_obj_tag(v_x_1400_) == 0)
{
lean_object* v___x_1401_; 
lean_dec(v_baseE_1398_);
lean_dec_ref(v_base_1397_);
v___x_1401_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__1, &lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___closed__1);
return v___x_1401_;
}
else
{
lean_object* v_head_1402_; lean_object* v_tail_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1414_; 
v_head_1402_ = lean_ctor_get(v_x_1400_, 0);
v_tail_1403_ = lean_ctor_get(v_x_1400_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1400_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1405_ = v_x_1400_;
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_tail_1403_);
lean_inc(v_head_1402_);
lean_dec(v_x_1400_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_inc(v_baseE_1398_);
lean_inc_ref(v_base_1397_);
v___x_1407_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg(v_base_1397_, v_baseE_1398_, v_x_1399_, v_head_1402_);
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_nat_add(v_x_1399_, v___x_1408_);
v___x_1410_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg(v_base_1397_, v_baseE_1398_, v___x_1409_, v_tail_1403_);
lean_dec(v___x_1409_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 1, v___x_1410_);
lean_ctor_set(v___x_1405_, 0, v___x_1407_);
v___x_1412_ = v___x_1405_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg___boxed(lean_object* v_base_1415_, lean_object* v_baseE_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg(v_base_1415_, v_baseE_1416_, v_x_1417_, v_x_1418_);
lean_dec(v_x_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion(lean_object* v_00_u03c3_1420_, lean_object* v_base_1421_, lean_object* v_baseE_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg(v_base_1421_, v_baseE_1422_, v_x_1423_, v_x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___boxed(lean_object* v_00_u03c3_1426_, lean_object* v_base_1427_, lean_object* v_baseE_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion(v_00_u03c3_1426_, v_base_1427_, v_baseE_1428_, v_x_1429_, v_x_1430_);
lean_dec(v_x_1429_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ProofProducing_0__Pancake_EmitCorrectCompose_emit_match__1_splitter___redArg(lean_object* v_x_1432_, lean_object* v_h__1_1433_, lean_object* v_h__2_1434_, lean_object* v_h__3_1435_){
_start:
{
switch(lean_obj_tag(v_x_1432_))
{
case 0:
{
lean_object* v_p_1436_; lean_object* v___x_1437_; 
lean_dec(v_h__3_1435_);
lean_dec(v_h__2_1434_);
v_p_1436_ = lean_ctor_get(v_x_1432_, 0);
lean_inc_ref(v_p_1436_);
lean_dec_ref(v_x_1432_);
v___x_1437_ = lean_apply_1(v_h__1_1433_, v_p_1436_);
return v___x_1437_;
}
case 1:
{
lean_object* v_s1_1438_; lean_object* v_s2_1439_; lean_object* v___x_1440_; 
lean_dec(v_h__3_1435_);
lean_dec(v_h__1_1433_);
v_s1_1438_ = lean_ctor_get(v_x_1432_, 0);
lean_inc_ref(v_s1_1438_);
v_s2_1439_ = lean_ctor_get(v_x_1432_, 1);
lean_inc_ref(v_s2_1439_);
lean_dec_ref(v_x_1432_);
v___x_1440_ = lean_apply_2(v_h__2_1434_, v_s1_1438_, v_s2_1439_);
return v___x_1440_;
}
default: 
{
lean_object* v_e_1441_; lean_object* v_guard_1442_; lean_object* v_s1_1443_; lean_object* v_s2_1444_; lean_object* v___x_1445_; 
lean_dec(v_h__2_1434_);
lean_dec(v_h__1_1433_);
v_e_1441_ = lean_ctor_get(v_x_1432_, 0);
lean_inc(v_e_1441_);
v_guard_1442_ = lean_ctor_get(v_x_1432_, 1);
lean_inc_ref(v_guard_1442_);
v_s1_1443_ = lean_ctor_get(v_x_1432_, 2);
lean_inc_ref(v_s1_1443_);
v_s2_1444_ = lean_ctor_get(v_x_1432_, 3);
lean_inc_ref(v_s2_1444_);
lean_dec_ref(v_x_1432_);
v___x_1445_ = lean_apply_4(v_h__3_1435_, v_e_1441_, v_guard_1442_, v_s1_1443_, v_s2_1444_);
return v___x_1445_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ProofProducing_0__Pancake_EmitCorrectCompose_emit_match__1_splitter(lean_object* v_00_u03c3_1446_, lean_object* v_motive_1447_, lean_object* v_x_1448_, lean_object* v_h__1_1449_, lean_object* v_h__2_1450_, lean_object* v_h__3_1451_){
_start:
{
switch(lean_obj_tag(v_x_1448_))
{
case 0:
{
lean_object* v_p_1452_; lean_object* v___x_1453_; 
lean_dec(v_h__3_1451_);
lean_dec(v_h__2_1450_);
v_p_1452_ = lean_ctor_get(v_x_1448_, 0);
lean_inc_ref(v_p_1452_);
lean_dec_ref(v_x_1448_);
v___x_1453_ = lean_apply_1(v_h__1_1449_, v_p_1452_);
return v___x_1453_;
}
case 1:
{
lean_object* v_s1_1454_; lean_object* v_s2_1455_; lean_object* v___x_1456_; 
lean_dec(v_h__3_1451_);
lean_dec(v_h__1_1449_);
v_s1_1454_ = lean_ctor_get(v_x_1448_, 0);
lean_inc_ref(v_s1_1454_);
v_s2_1455_ = lean_ctor_get(v_x_1448_, 1);
lean_inc_ref(v_s2_1455_);
lean_dec_ref(v_x_1448_);
v___x_1456_ = lean_apply_2(v_h__2_1450_, v_s1_1454_, v_s2_1455_);
return v___x_1456_;
}
default: 
{
lean_object* v_e_1457_; lean_object* v_guard_1458_; lean_object* v_s1_1459_; lean_object* v_s2_1460_; lean_object* v___x_1461_; 
lean_dec(v_h__2_1450_);
lean_dec(v_h__1_1449_);
v_e_1457_ = lean_ctor_get(v_x_1448_, 0);
lean_inc(v_e_1457_);
v_guard_1458_ = lean_ctor_get(v_x_1448_, 1);
lean_inc_ref(v_guard_1458_);
v_s1_1459_ = lean_ctor_get(v_x_1448_, 2);
lean_inc_ref(v_s1_1459_);
v_s2_1460_ = lean_ctor_get(v_x_1448_, 3);
lean_inc_ref(v_s2_1460_);
lean_dec_ref(v_x_1448_);
v___x_1461_ = lean_apply_4(v_h__3_1451_, v_e_1457_, v_guard_1458_, v_s1_1459_, v_s2_1460_);
return v___x_1461_;
}
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__0(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = lean_unsigned_to_nat(72u);
v___x_1463_ = lean_unsigned_to_nat(64u);
v___x_1464_ = l_BitVec_ofNat(v___x_1463_, v___x_1462_);
return v___x_1464_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__1(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_unsigned_to_nat(84u);
v___x_1466_ = lean_unsigned_to_nat(64u);
v___x_1467_ = l_BitVec_ofNat(v___x_1466_, v___x_1465_);
return v___x_1467_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__2(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = lean_unsigned_to_nat(80u);
v___x_1469_ = lean_unsigned_to_nat(64u);
v___x_1470_ = l_BitVec_ofNat(v___x_1469_, v___x_1468_);
return v___x_1470_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__3(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__2, &lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__2);
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___x_1471_);
return v___x_1473_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__4(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__3, &lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__3);
v___x_1475_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__1, &lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__1);
v___x_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
lean_ctor_set(v___x_1476_, 1, v___x_1474_);
return v___x_1476_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__5(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__4, &lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__4);
v___x_1478_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__1, &lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__1);
v___x_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1477_);
return v___x_1479_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__6(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1480_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__5, &lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__5);
v___x_1481_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__0, &lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__0);
v___x_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1480_);
return v___x_1482_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes(void){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__6, &lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes___closed__6);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg(lean_object* v_bufVal_1487_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1488_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg___closed__1));
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes;
v___x_1491_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteRegion___redArg(v_bufVal_1487_, v___x_1488_, v___x_1489_, v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp(lean_object* v_00_u03c3_1492_, lean_object* v_bufVal_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg(v_bufVal_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp__translated___redArg(lean_object* v_bufVal_1495_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg(v_bufVal_1495_);
v___x_1497_ = lp_orb_x2dcompiler_Pancake_EmitCorrectCompose_emit___redArg(v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp__translated(lean_object* v_00_u03c3_1498_, lean_object* v_o_1499_, lean_object* v_bufVal_1500_, lean_object* v_hbuf_1501_, lean_object* v_hregion_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp__translated___redArg(v_bufVal_1500_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp__translated___boxed(lean_object* v_00_u03c3_1504_, lean_object* v_o_1505_, lean_object* v_bufVal_1506_, lean_object* v_hbuf_1507_, lean_object* v_hregion_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp__translated(v_00_u03c3_1504_, v_o_1505_, v_bufVal_1506_, v_hbuf_1507_, v_hregion_1508_);
lean_dec_ref(v_o_1505_);
return v_res_1509_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__0(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_unsigned_to_nat(13u);
v___x_1511_ = lean_unsigned_to_nat(64u);
v___x_1512_ = l_BitVec_ofNat(v___x_1511_, v___x_1510_);
return v___x_1512_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_unsigned_to_nat(10u);
v___x_1514_ = lean_unsigned_to_nat(64u);
v___x_1515_ = l_BitVec_ofNat(v___x_1514_, v___x_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg(lean_object* v_bufVal_1516_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1517_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg___closed__1));
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__0, &lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__0);
lean_inc_ref(v_bufVal_1516_);
v___x_1520_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg(v_bufVal_1516_, v___x_1517_, v___x_1518_, v___x_1519_);
v___x_1521_ = lean_unsigned_to_nat(1u);
v___x_1522_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__1, &lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg___closed__1);
v___x_1523_ = lp_orb_x2dcompiler_Pancake_ProofProducing_byteLeaf___redArg(v_bufVal_1516_, v___x_1517_, v___x_1521_, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1520_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp(lean_object* v_00_u03c3_1525_, lean_object* v_bufVal_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = lp_orb_x2dcompiler_Pancake_ProofProducing_crlfStamp___redArg(v_bufVal_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_sampleBufVal___redArg(lean_object* v_s_1528_){
_start:
{
lean_object* v_locals_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_locals_1529_ = lean_ctor_get(v_s_1528_, 0);
lean_inc_ref(v_locals_1529_);
lean_dec_ref(v_s_1528_);
v___x_1530_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ProofProducing_httpStamp___redArg___closed__0));
v___x_1531_ = lean_apply_1(v_locals_1529_, v___x_1530_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1, &lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ProofProducing_closedDemo___closed__1);
return v___x_1532_;
}
else
{
lean_object* v_val_1533_; 
v_val_1533_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1533_);
lean_dec_ref(v___x_1531_);
return v_val_1533_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ProofProducing_sampleBufVal(lean_object* v_00_u03c3_1534_, lean_object* v_s_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = lp_orb_x2dcompiler_Pancake_ProofProducing_sampleBufVal___redArg(v_s_1535_);
return v___x_1536_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_EmitCorrectCompose(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_EmitCorrectClock(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_ProofProducing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_EmitCorrectCompose(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_EmitCorrectClock(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes = _init_lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ProofProducing_httpBytes);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
