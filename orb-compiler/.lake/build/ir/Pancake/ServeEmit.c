// Lean compiler output
// Module: Pancake.ServeEmit
// Imports: public import Init public meta import Init public import Pancake.ServeSlice public import Dsl.EmitPancake
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
lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eEq(lean_object*, lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405;
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp200;
lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eLt(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_IO_println___at___00Dsl_EmitPancake_main_spec__0(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eMul(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_bytesOf_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_bytesOf(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_storesInto_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_storesInto(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__0_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__2_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "req"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__3_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__3_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__7;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__0_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(72) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__11_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__12;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__13_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__0_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__13_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__14_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__15 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__15_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(79) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__16 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__16_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__17;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__18 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__18_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__0_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__18_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__19 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__19_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__20 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__20_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(80) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__21 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__21_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__22;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__23;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__24;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__25;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__26 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__26_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__0_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__26_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__27 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__27_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__28 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__28_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__0_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__29 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__29_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__30 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__30_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__31;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__32;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__33;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__34;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__35;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__36;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__37;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__38;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__39;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__40;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__41;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "serve"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ctrl"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__3_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__3_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "len"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__4_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__4_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__5_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "out"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__7_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__8_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__5_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__9 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__9_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__3_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__9_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__10 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__10_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__2_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__10_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__11 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__11_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "count"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__12 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__12_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__12_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__13 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__13_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__14 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__14_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__15 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__15_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__16;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__12_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__17 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__17_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__17_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__18 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__18_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__19 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__19_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport(lean_object*, lean_object*);
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_be4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_be4___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_be4___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_be4(lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "clen"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "serve_cfg"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hsts"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__1_value),((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__8_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__2_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__3 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__3_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__6;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__7_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__8;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_banner___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 358, .m_capacity = 358, .m_length = 357, .m_data = "// GENERATED by Pancake/ServeEmit.lean -- do not hand-edit.\n// routed serve slice as a C-callable export fun (SysV ABI: ctrl/req/len/out).\n// Emission is generative: this file is ppFun applied to the built PFun; the\n// stored response bytes are `serialize resp200` / `serialize resp405`.\n// Compile: cake --pancake --main_return=true < serve.pnk > serve.S\n\n"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_banner___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_banner___closed__0_value;
LEAN_EXPORT const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_banner = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_banner___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__6;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Pancake/serve_slice_export.pnk"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__0_value;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "wrote Pancake/serve_slice_export.pnk ("};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__4;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " bytes)"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__5_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__6;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk();
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_writeGolden_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Pancake/serve_resp200.bin"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__3;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Pancake/serve_resp405.bin"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__4 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__4_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__5;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__6;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__7;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "wrote Pancake/serve_resp200.bin, Pancake/serve_resp405.bin"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__8 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__8_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden();
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_bytesOf_spec__0(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = l_List_reverse___redArg(v_a_2_);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_13_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
v_isSharedCheck_13_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_13_ == 0)
{
v___x_7_ = v_a_1_;
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_a_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_10_; 
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_a_2_);
v___x_10_ = v___x_7_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v_head_4_);
lean_ctor_set(v_reuseFailAlloc_12_, 1, v_a_2_);
v___x_10_ = v_reuseFailAlloc_12_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
v_a_1_ = v_tail_5_;
v_a_2_ = v___x_10_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_bytesOf(lean_object* v_bs_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_box(0);
v___x_16_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_bytesOf_spec__0(v_bs_14_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_storesInto_spec__0(lean_object* v_dst_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
if (lean_obj_tag(v_a_18_) == 0)
{
lean_object* v___x_20_; 
lean_dec_ref(v_dst_17_);
v___x_20_ = l_List_reverse___redArg(v_a_19_);
return v___x_20_;
}
else
{
lean_object* v_head_21_; lean_object* v_tail_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_42_; 
v_head_21_ = lean_ctor_get(v_a_18_, 0);
v_tail_22_ = lean_ctor_get(v_a_18_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_a_18_);
if (v_isSharedCheck_42_ == 0)
{
v___x_24_ = v_a_18_;
v_isShared_25_ = v_isSharedCheck_42_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_tail_22_);
lean_inc(v_head_21_);
lean_dec(v_a_18_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_42_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v_fst_26_; lean_object* v_snd_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_41_; 
v_fst_26_ = lean_ctor_get(v_head_21_, 0);
v_snd_27_ = lean_ctor_get(v_head_21_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v_head_21_);
if (v_isSharedCheck_41_ == 0)
{
v___x_29_ = v_head_21_;
v_isShared_30_ = v_isSharedCheck_41_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_snd_27_);
lean_inc(v_fst_26_);
lean_dec(v_head_21_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_41_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
lean_inc_ref(v_dst_17_);
v___x_31_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_31_, 0, v_dst_17_);
v___x_32_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_31_, v_fst_26_);
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v_snd_27_);
if (v_isShared_30_ == 0)
{
lean_ctor_set_tag(v___x_29_, 3);
lean_ctor_set(v___x_29_, 1, v___x_33_);
lean_ctor_set(v___x_29_, 0, v___x_32_);
v___x_35_ = v___x_29_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v___x_33_);
v___x_35_ = v_reuseFailAlloc_40_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_37_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 1, v_a_19_);
lean_ctor_set(v___x_24_, 0, v___x_35_);
v___x_37_ = v___x_24_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_a_19_);
v___x_37_ = v_reuseFailAlloc_39_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
v_a_18_ = v_tail_22_;
v_a_19_ = v___x_37_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_storesInto(lean_object* v_dst_43_, lean_object* v_bs_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_45_ = l_List_lengthTR___redArg(v_bs_44_);
v___x_46_ = l_List_range(v___x_45_);
v___x_47_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v___x_46_, v_bs_44_);
v___x_48_ = lean_box(0);
v___x_49_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_storesInto_spec__0(v_dst_43_, v___x_47_, v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__7(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__6));
v___x_64_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__5));
v___x_65_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eEq(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__12(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__11));
v___x_77_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__5));
v___x_78_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eEq(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__17(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__16));
v___x_90_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__5));
v___x_91_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eEq(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__22(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__21));
v___x_103_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__5));
v___x_104_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eEq(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__23(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__4));
v___x_107_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__24(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__23, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__23_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__23);
v___x_109_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__25(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__16));
v___x_111_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__24, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__24_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__24);
v___x_112_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eEq(v___x_111_, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__31(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_127_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__30));
v___x_128_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__28));
v___x_129_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__25, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__25_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__25);
v___x_130_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
lean_ctor_set(v___x_130_, 2, v___x_127_);
return v___x_130_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__32(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_box(0);
v___x_132_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__31, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__31_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__31);
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
return v___x_133_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__33(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__30));
v___x_135_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__32, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__32_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__32);
v___x_136_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__22, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__22_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__22);
v___x_137_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
lean_ctor_set(v___x_137_, 2, v___x_134_);
return v___x_137_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__34(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_box(0);
v___x_139_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__33, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__33_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__33);
v___x_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
return v___x_140_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__35(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__34, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__34_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__34);
v___x_142_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__20));
v___x_143_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__17, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__17);
v___x_144_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
lean_ctor_set(v___x_144_, 2, v___x_141_);
return v___x_144_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__36(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_box(0);
v___x_146_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__35, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__35_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__35);
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__37(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_148_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__36, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__36_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__36);
v___x_149_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__15));
v___x_150_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__12, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__12);
v___x_151_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
lean_ctor_set(v___x_151_, 2, v___x_148_);
return v___x_151_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__38(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_box(0);
v___x_153_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__37, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__37_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__37);
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__39(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_155_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__38, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__38_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__38);
v___x_156_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__10));
v___x_157_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__7, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__7);
v___x_158_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v___x_155_);
return v___x_158_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__40(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_box(0);
v___x_160_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__39, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__39_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__39);
v___x_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__41(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__40, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__40_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__40);
v___x_163_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__2));
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
return v___x_164_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod(void){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__41, &lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__41_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__41);
return v___x_165_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__16(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__15));
v___x_203_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__14));
v___x_204_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eLt(v___x_203_, v___x_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport(lean_object* v_bs200_212_, lean_object* v_bs405_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; 
v___x_214_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__0));
v___x_215_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__6));
v___x_216_ = lean_box(0);
v___x_217_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__11));
v___x_218_ = lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod;
v___x_219_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__12));
v___x_220_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__13));
v___x_221_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__16, &lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__16_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__16);
lean_inc(v_bs200_212_);
v___x_222_ = lp_orb_x2dcompiler_Pancake_ServeEmit_storesInto(v___x_215_, v_bs200_212_);
v___x_223_ = l_List_lengthTR___redArg(v_bs200_212_);
lean_dec(v_bs200_212_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
v___x_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_219_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_216_);
v___x_227_ = l_List_appendTR___redArg(v___x_222_, v___x_226_);
lean_inc(v_bs405_213_);
v___x_228_ = lp_orb_x2dcompiler_Pancake_ServeEmit_storesInto(v___x_215_, v_bs405_213_);
v___x_229_ = l_List_lengthTR___redArg(v_bs405_213_);
lean_dec(v_bs405_213_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
v___x_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_219_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_216_);
v___x_233_ = l_List_appendTR___redArg(v___x_228_, v___x_232_);
v___x_234_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_234_, 0, v___x_221_);
lean_ctor_set(v___x_234_, 1, v___x_227_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
v___x_235_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__19));
v___x_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_220_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = l_List_appendTR___redArg(v___x_218_, v___x_237_);
v___x_239_ = 1;
v___x_240_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_240_, 0, v___x_214_);
lean_ctor_set(v___x_240_, 1, v___x_217_);
lean_ctor_set(v___x_240_, 2, v___x_238_);
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*3, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_be4(lean_object* v_cfgPtr_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_244_ = lean_unsigned_to_nat(0u);
lean_inc_n(v_cfgPtr_243_, 3);
v___x_245_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v_cfgPtr_243_, v___x_244_);
v___x_246_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
v___x_247_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_be4___closed__0));
v___x_248_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eMul(v___x_246_, v___x_247_);
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v_cfgPtr_243_, v___x_249_);
v___x_251_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
v___x_252_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_248_, v___x_251_);
v___x_253_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eMul(v___x_252_, v___x_247_);
v___x_254_ = lean_unsigned_to_nat(2u);
v___x_255_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v_cfgPtr_243_, v___x_254_);
v___x_256_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
v___x_257_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_253_, v___x_256_);
v___x_258_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eMul(v___x_257_, v___x_247_);
v___x_259_ = lean_unsigned_to_nat(3u);
v___x_260_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v_cfgPtr_243_, v___x_259_);
v___x_261_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
v___x_262_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eAdd(v___x_258_, v___x_261_);
return v___x_262_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__2(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__8));
v___x_267_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__1));
v___x_268_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eEq(v___x_267_, v___x_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg(lean_object* v_cfgPtr_269_, lean_object* v_tog_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_271_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__0));
v___x_272_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_272_, 0, v_cfgPtr_269_);
lean_inc_ref(v___x_272_);
v___x_273_ = lp_orb_x2dcompiler_Pancake_ServeEmit_be4(v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_271_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__2, &lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg___closed__2);
v___x_276_ = lean_box(0);
v___x_277_ = lean_unsigned_to_nat(4u);
v___x_278_ = lp_orb_x2dcompiler_Dsl_EmitPancake_atOff(v___x_272_, v___x_277_);
v___x_279_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v_tog_270_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_276_);
v___x_282_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_282_, 0, v___x_275_);
lean_ctor_set(v___x_282_, 1, v___x_276_);
lean_ctor_set(v___x_282_, 2, v___x_281_);
v___x_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_276_);
v___x_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_274_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__4(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__3));
v___x_294_ = lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod;
v___x_295_ = l_List_appendTR___redArg(v___x_294_, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__5(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__1));
v___x_297_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__1));
v___x_298_ = lp_orb_x2dcompiler_Pancake_ServeEmit_readCfg(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__6(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__5, &lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__5);
v___x_300_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__4, &lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__4);
v___x_301_ = l_List_appendTR___redArg(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__8(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod___closed__8));
v___x_305_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__7));
v___x_306_ = lp_orb_x2dcompiler_Dsl_EmitPancake_eEq(v___x_305_, v___x_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg(lean_object* v_bs200_307_, lean_object* v_bs200Alt_308_, lean_object* v_bs405_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; 
v___x_310_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__0));
v___x_311_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__6));
v___x_312_ = lean_box(0);
v___x_313_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__11));
v___x_314_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__6, &lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__6);
v___x_315_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__12));
v___x_316_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__13));
v___x_317_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__16, &lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__16_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__16);
v___x_318_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__8, &lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_serveExportCfg___closed__8);
lean_inc(v_bs200_307_);
v___x_319_ = lp_orb_x2dcompiler_Pancake_ServeEmit_storesInto(v___x_311_, v_bs200_307_);
v___x_320_ = l_List_lengthTR___redArg(v_bs200_307_);
lean_dec(v_bs200_307_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
v___x_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_315_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_312_);
v___x_324_ = l_List_appendTR___redArg(v___x_319_, v___x_323_);
lean_inc(v_bs200Alt_308_);
v___x_325_ = lp_orb_x2dcompiler_Pancake_ServeEmit_storesInto(v___x_311_, v_bs200Alt_308_);
v___x_326_ = l_List_lengthTR___redArg(v_bs200Alt_308_);
lean_dec(v_bs200Alt_308_);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_315_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_312_);
v___x_330_ = l_List_appendTR___redArg(v___x_325_, v___x_329_);
v___x_331_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_331_, 0, v___x_318_);
lean_ctor_set(v___x_331_, 1, v___x_324_);
lean_ctor_set(v___x_331_, 2, v___x_330_);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_312_);
lean_inc(v_bs405_309_);
v___x_333_ = lp_orb_x2dcompiler_Pancake_ServeEmit_storesInto(v___x_311_, v_bs405_309_);
v___x_334_ = l_List_lengthTR___redArg(v_bs405_309_);
lean_dec(v_bs405_309_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_315_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_312_);
v___x_338_ = l_List_appendTR___redArg(v___x_333_, v___x_337_);
v___x_339_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_339_, 0, v___x_317_);
lean_ctor_set(v___x_339_, 1, v___x_332_);
lean_ctor_set(v___x_339_, 2, v___x_338_);
v___x_340_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport___closed__19));
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_316_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = l_List_appendTR___redArg(v___x_314_, v___x_342_);
v___x_344_ = 1;
v___x_345_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_345_, 0, v___x_310_);
lean_ctor_set(v___x_345_, 1, v___x_313_);
lean_ctor_set(v___x_345_, 2, v___x_343_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*3, v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__0(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lp_orb_x2dcompiler_Pancake_ServeSlice_resp200;
v___x_349_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__1(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__0, &lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__0);
v___x_351_ = lp_orb_x2dcompiler_Pancake_ServeEmit_bytesOf(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__2(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lp_orb_x2dcompiler_Pancake_ServeSlice_resp405;
v___x_353_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__3(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__2, &lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__2);
v___x_355_ = lp_orb_x2dcompiler_Pancake_ServeEmit_bytesOf(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__4(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__3, &lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__3);
v___x_357_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__1, &lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__1);
v___x_358_ = lp_orb_x2dcompiler_Pancake_ServeEmit_serveExport(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__5(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__4, &lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__4);
v___x_360_ = lp_orb_x2dcompiler_Dsl_EmitPancake_ppFun(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__6(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__5, &lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__5);
v___x_362_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_banner___closed__0));
v___x_363_ = lean_string_append(v___x_362_, v___x_361_);
return v___x_363_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk(void){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__6, &lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__6);
return v___x_364_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__2(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk;
v___x_368_ = lean_string_length(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__3(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__2, &lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__2);
v___x_370_ = l_Nat_reprFast(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__4(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__3, &lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__3);
v___x_372_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__1));
v___x_373_ = lean_string_append(v___x_372_, v___x_371_);
return v___x_373_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__6(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__5));
v___x_376_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__4, &lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__4);
v___x_377_ = lean_string_append(v___x_376_, v___x_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk(){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__0));
v___x_380_ = lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk;
v___x_381_ = l_IO_FS_writeFile(v___x_379_, v___x_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec_ref(v___x_381_);
v___x_382_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__6, &lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___closed__6);
v___x_383_ = lp_orb_x2dcompiler_IO_println___at___00Dsl_EmitPancake_main_spec__0(v___x_382_);
return v___x_383_;
}
else
{
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk___boxed(lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = lp_orb_x2dcompiler_Pancake_ServeEmit_writePnk();
return v_res_385_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_writeGolden_spec__0(lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
if (lean_obj_tag(v_a_386_) == 0)
{
lean_object* v___x_388_; 
v___x_388_ = l_List_reverse___redArg(v_a_387_);
return v___x_388_;
}
else
{
lean_object* v_head_389_; lean_object* v_tail_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_400_; 
v_head_389_ = lean_ctor_get(v_a_386_, 0);
v_tail_390_ = lean_ctor_get(v_a_386_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_a_386_);
if (v_isSharedCheck_400_ == 0)
{
v___x_392_ = v_a_386_;
v_isShared_393_ = v_isSharedCheck_400_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_tail_390_);
lean_inc(v_head_389_);
lean_dec(v_a_386_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_400_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_394_ = lean_uint8_of_nat(v_head_389_);
lean_dec(v_head_389_);
v___x_395_ = lean_box(v___x_394_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v_a_387_);
lean_ctor_set(v___x_392_, 0, v___x_395_);
v___x_397_ = v___x_392_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_a_387_);
v___x_397_ = v_reuseFailAlloc_399_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
v_a_386_ = v_tail_390_;
v_a_387_ = v___x_397_;
goto _start;
}
}
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__1(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_box(0);
v___x_403_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__1, &lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__1);
v___x_404_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_writeGolden_spec__0(v___x_403_, v___x_402_);
return v___x_404_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__2(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__1, &lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__1);
v___x_406_ = lean_array_mk(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__3(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__2, &lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__2);
v___x_408_ = lean_byte_array_mk(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__5(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_box(0);
v___x_411_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__3, &lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk___closed__3);
v___x_412_ = lp_orb_x2dcompiler_List_mapTR_loop___at___00Pancake_ServeEmit_writeGolden_spec__0(v___x_411_, v___x_410_);
return v___x_412_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__6(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__5, &lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__5);
v___x_414_ = lean_array_mk(v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__7(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__6, &lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__6_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__6);
v___x_416_ = lean_byte_array_mk(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden(){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__0));
v___x_420_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__3, &lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__3);
v___x_421_ = l_IO_FS_writeBinFile(v___x_419_, v___x_420_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v___x_421_);
v___x_422_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__4));
v___x_423_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__7, &lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__7);
v___x_424_ = l_IO_FS_writeBinFile(v___x_422_, v___x_423_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec_ref(v___x_424_);
v___x_425_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___closed__8));
v___x_426_ = lp_orb_x2dcompiler_IO_println___at___00Dsl_EmitPancake_main_spec__0(v___x_425_);
return v___x_426_;
}
else
{
return v___x_424_;
}
}
else
{
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden___boxed(lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = lp_orb_x2dcompiler_Pancake_ServeEmit_writeGolden();
return v_res_428_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_ServeSlice(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Dsl_EmitPancake(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_ServeEmit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_ServeSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Dsl_EmitPancake(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod = _init_lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ServeEmit_parseMethod);
lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk = _init_lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ServeEmit_servePnk);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
