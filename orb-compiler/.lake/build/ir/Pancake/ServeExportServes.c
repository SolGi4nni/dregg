// Lean compiler output
// Module: Pancake.ServeExportServes
// Imports: public import Init public meta import Init public import Pancake.LowerBridgeSem
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
extern lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp200;
lean_object* lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_ServeEmit_bytesOf(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_LowerBridge_addrModel(lean_object*, lean_object*);
extern lean_object* lp_orb_x2dcompiler_Pancake_ServeSlice_resp405;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_storeAssignModel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_storeAssignModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_ServeExportServes_storeAssignModel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_ServeExportServes_storeAssignModel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "req"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__1_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__1_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__2 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__2_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__4;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__5;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__6_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__7;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__8;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__9;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__10;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__11;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__12;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__13;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__14;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__15;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__16;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__17;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__18;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__19;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__20;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__21;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__22;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__23;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__24;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__25;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__26;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__27;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__28;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__29;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__30;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__31;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__32;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__33;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__34;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__35;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__36;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__37;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__38;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "count"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__0_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__2;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__3;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__4;
static const lean_string_object lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "out"};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__5 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__5_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__0_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__6 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__6_value;
static const lean_ctor_object lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__6_value)}};
static const lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__7 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__7_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerExp_match__6_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerExp_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerExp_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerExp_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmt1_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmt1_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmtsFold_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmtsFold_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmt1_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmt1_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__0;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_storeAssignModel(lean_object* v_dst_1_, lean_object* v_cnt_2_, lean_object* v_k_3_, lean_object* v_x_4_){
_start:
{
if (lean_obj_tag(v_x_4_) == 0)
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
lean_dec_ref(v_dst_1_);
v___x_5_ = lean_unsigned_to_nat(64u);
v___x_6_ = l_BitVec_ofNat(v___x_5_, v_k_3_);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
v___x_8_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_8_, 0, v_cnt_2_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v_head_9_; lean_object* v_tail_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_31_; 
v_head_9_ = lean_ctor_get(v_x_4_, 0);
v_tail_10_ = lean_ctor_get(v_x_4_, 1);
v_isSharedCheck_31_ = !lean_is_exclusive(v_x_4_);
if (v_isSharedCheck_31_ == 0)
{
v___x_12_ = v_x_4_;
v_isShared_13_ = v_isSharedCheck_31_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_tail_10_);
lean_inc(v_head_9_);
lean_dec(v_x_4_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_31_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v_fst_14_; lean_object* v_snd_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_30_; 
v_fst_14_ = lean_ctor_get(v_head_9_, 0);
v_snd_15_ = lean_ctor_get(v_head_9_, 1);
v_isSharedCheck_30_ = !lean_is_exclusive(v_head_9_);
if (v_isSharedCheck_30_ == 0)
{
v___x_17_ = v_head_9_;
v_isShared_18_ = v_isSharedCheck_30_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_snd_15_);
lean_inc(v_fst_14_);
lean_dec(v_head_9_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_30_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_24_; 
lean_inc_ref(v_dst_1_);
v___x_19_ = lp_orb_x2dcompiler_Pancake_LowerBridge_addrModel(v_dst_1_, v_fst_14_);
lean_dec(v_fst_14_);
v___x_20_ = lean_unsigned_to_nat(64u);
v___x_21_ = l_BitVec_ofNat(v___x_20_, v_snd_15_);
lean_dec(v_snd_15_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
if (v_isShared_18_ == 0)
{
lean_ctor_set_tag(v___x_17_, 9);
lean_ctor_set(v___x_17_, 1, v___x_22_);
lean_ctor_set(v___x_17_, 0, v___x_19_);
v___x_24_ = v___x_17_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v___x_22_);
v___x_24_ = v_reuseFailAlloc_29_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_25_ = lp_orb_x2dcompiler_Pancake_ServeExportServes_storeAssignModel(v_dst_1_, v_cnt_2_, v_k_3_, v_tail_10_);
if (v_isShared_13_ == 0)
{
lean_ctor_set_tag(v___x_12_, 5);
lean_ctor_set(v___x_12_, 1, v___x_25_);
lean_ctor_set(v___x_12_, 0, v___x_24_);
v___x_27_ = v___x_12_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v___x_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_storeAssignModel___boxed(lean_object* v_dst_32_, lean_object* v_cnt_33_, lean_object* v_k_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_orb_x2dcompiler_Pancake_ServeExportServes_storeAssignModel(v_dst_32_, v_cnt_33_, v_k_34_, v_x_35_);
lean_dec(v_k_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_ServeExportServes_storeAssignModel_match__1_splitter___redArg(lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_39_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__1_38_, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v_head_42_; lean_object* v_tail_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_38_);
v_head_42_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_head_42_);
v_tail_43_ = lean_ctor_get(v_x_37_, 1);
lean_inc(v_tail_43_);
lean_dec_ref(v_x_37_);
v___x_44_ = lean_apply_2(v_h__2_39_, v_head_42_, v_tail_43_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_ServeExportServes_storeAssignModel_match__1_splitter(lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_48_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__1_47_, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v_head_51_; lean_object* v_tail_52_; lean_object* v___x_53_; 
lean_dec(v_h__1_47_);
v_head_51_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_51_);
v_tail_52_ = lean_ctor_get(v_x_46_, 1);
lean_inc(v_tail_52_);
lean_dec_ref(v_x_46_);
v___x_53_ = lean_apply_2(v_h__2_48_, v_head_51_, v_tail_52_);
return v___x_53_;
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_unsigned_to_nat(71u);
v___x_60_ = lean_unsigned_to_nat(64u);
v___x_61_ = l_BitVec_ofNat(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__4(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__3, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__3);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__5(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__4, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__4);
v___x_65_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__2));
v___x_66_ = 1;
v___x_67_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_67_, 0, v___x_65_);
lean_ctor_set(v___x_67_, 1, v___x_64_);
lean_ctor_set_uint8(v___x_67_, sizeof(void*)*2, v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__7(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_unsigned_to_nat(64u);
v___x_71_ = l_BitVec_ofNat(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__8(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__7, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__7_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__7);
v___x_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__9(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__8, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__8);
v___x_75_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__6));
v___x_76_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
return v___x_76_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__10(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_unsigned_to_nat(72u);
v___x_78_ = lean_unsigned_to_nat(64u);
v___x_79_ = l_BitVec_ofNat(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__11(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__10, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__10_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__10);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__12(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; 
v___x_82_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__11, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__11_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__11);
v___x_83_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__2));
v___x_84_ = 1;
v___x_85_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_82_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*2, v___x_84_);
return v___x_85_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__13(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_unsigned_to_nat(2u);
v___x_87_ = lean_unsigned_to_nat(64u);
v___x_88_ = l_BitVec_ofNat(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__14(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__13, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__13_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__13);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__15(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__14, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__14_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__14);
v___x_92_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__6));
v___x_93_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__16(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_unsigned_to_nat(79u);
v___x_95_ = lean_unsigned_to_nat(64u);
v___x_96_ = l_BitVec_ofNat(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__17(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__16, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__16_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__16);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__18(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__17, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__17);
v___x_100_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__2));
v___x_101_ = 1;
v___x_102_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_99_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*2, v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__19(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_unsigned_to_nat(3u);
v___x_104_ = lean_unsigned_to_nat(64u);
v___x_105_ = l_BitVec_ofNat(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__20(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__19, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__19_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__19);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__21(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__20, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__20_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__20);
v___x_109_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__6));
v___x_110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__22(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_unsigned_to_nat(80u);
v___x_112_ = lean_unsigned_to_nat(64u);
v___x_113_ = l_BitVec_ofNat(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__23(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__22, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__22_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__22);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__24(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; 
v___x_116_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__23, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__23_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__23);
v___x_117_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__2));
v___x_118_ = 1;
v___x_119_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set(v___x_119_, 1, v___x_116_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*2, v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__25(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_unsigned_to_nat(64u);
v___x_122_ = l_BitVec_ofNat(v___x_121_, v___x_120_);
return v___x_122_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__26(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__25, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__25_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__25);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__27(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; 
v___x_125_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__26, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__26_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__26);
v___x_126_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__1));
v___x_127_ = 0;
v___x_128_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_125_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*2, v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__28(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__27, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__27_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__27);
v___x_130_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__29(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; lean_object* v___x_134_; 
v___x_131_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__17, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__17_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__17);
v___x_132_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__28, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__28_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__28);
v___x_133_ = 1;
v___x_134_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set(v___x_134_, 1, v___x_131_);
lean_ctor_set_uint8(v___x_134_, sizeof(void*)*2, v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__30(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__26, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__26_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__26);
v___x_136_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__6));
v___x_137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
return v___x_137_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__31(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_unsigned_to_nat(9u);
v___x_139_ = lean_unsigned_to_nat(64u);
v___x_140_ = l_BitVec_ofNat(v___x_139_, v___x_138_);
return v___x_140_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__32(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__31, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__31_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__31);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__33(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__32, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__32_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__32);
v___x_144_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__6));
v___x_145_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__34(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__33, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__33_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__33);
v___x_147_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__30, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__30_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__30);
v___x_148_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__29, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__29_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__29);
v___x_149_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
lean_ctor_set(v___x_149_, 2, v___x_146_);
return v___x_149_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__35(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__33, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__33_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__33);
v___x_151_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__34, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__34_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__34);
v___x_152_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__24, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__24_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__24);
v___x_153_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
lean_ctor_set(v___x_153_, 2, v___x_150_);
return v___x_153_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__36(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__35, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__35_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__35);
v___x_155_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__21, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__21_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__21);
v___x_156_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__18, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__18_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__18);
v___x_157_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
lean_ctor_set(v___x_157_, 2, v___x_154_);
return v___x_157_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__37(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_158_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__36, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__36_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__36);
v___x_159_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__15, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__15_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__15);
v___x_160_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__12, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__12_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__12);
v___x_161_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
lean_ctor_set(v___x_161_, 2, v___x_158_);
return v___x_161_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__38(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_162_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__37, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__37_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__37);
v___x_163_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__9, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__9_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__9);
v___x_164_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__5, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__5_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__5);
v___x_165_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
lean_ctor_set(v___x_165_, 2, v___x_162_);
return v___x_165_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__38, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__38_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__38);
return v___x_166_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__2(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_unsigned_to_nat(4u);
v___x_171_ = lean_unsigned_to_nat(64u);
v___x_172_ = l_BitVec_ofNat(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__3(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__2, &lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__2);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__4(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__3, &lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__3_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__3);
v___x_176_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__1));
v___x_177_ = 0;
v___x_178_ = lean_alloc_ctor(5, 2, 1);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_175_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*2, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel(lean_object* v_bs200_184_, lean_object* v_bs405_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_186_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__6));
v___x_187_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__32, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__32_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__32);
v___x_188_ = lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel;
v___x_189_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__0));
v___x_190_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__8, &lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__8_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel___closed__8);
v___x_191_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__4, &lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__4_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__4);
v___x_192_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__5));
v___x_193_ = l_List_lengthTR___redArg(v_bs200_184_);
lean_inc(v___x_193_);
v___x_194_ = l_List_range(v___x_193_);
v___x_195_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v___x_194_, v_bs200_184_);
v___x_196_ = lp_orb_x2dcompiler_Pancake_ServeExportServes_storeAssignModel(v___x_192_, v___x_189_, v___x_193_, v___x_195_);
lean_dec(v___x_193_);
v___x_197_ = l_List_lengthTR___redArg(v_bs405_185_);
lean_inc(v___x_197_);
v___x_198_ = l_List_range(v___x_197_);
v___x_199_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v___x_198_, v_bs405_185_);
v___x_200_ = lp_orb_x2dcompiler_Pancake_ServeExportServes_storeAssignModel(v___x_192_, v___x_189_, v___x_197_, v___x_199_);
lean_dec(v___x_197_);
v___x_201_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_201_, 0, v___x_191_);
lean_ctor_set(v___x_201_, 1, v___x_196_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
v___x_202_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_ServeExportServes_serveModel___closed__7));
v___x_203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_204_, 0, v___x_189_);
lean_ctor_set(v___x_204_, 1, v___x_190_);
lean_ctor_set(v___x_204_, 2, v___x_203_);
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_188_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_206_, 0, v___x_186_);
lean_ctor_set(v___x_206_, 1, v___x_187_);
lean_ctor_set(v___x_206_, 2, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerExp_match__6_splitter___redArg(lean_object* v_x_207_, lean_object* v_h__1_208_, lean_object* v_h__2_209_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v_h__1_208_);
v___x_210_ = lean_box(0);
v___x_211_ = lean_apply_1(v_h__2_209_, v___x_210_);
return v___x_211_;
}
else
{
lean_object* v_val_212_; lean_object* v___x_213_; 
lean_dec(v_h__2_209_);
v_val_212_ = lean_ctor_get(v_x_207_, 0);
lean_inc(v_val_212_);
lean_dec_ref(v_x_207_);
v___x_213_ = lean_apply_1(v_h__1_208_, v_val_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerExp_match__6_splitter(lean_object* v_motive_214_, lean_object* v_x_215_, lean_object* v_h__1_216_, lean_object* v_h__2_217_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v_h__1_216_);
v___x_218_ = lean_box(0);
v___x_219_ = lean_apply_1(v_h__2_217_, v___x_218_);
return v___x_219_;
}
else
{
lean_object* v_val_220_; lean_object* v___x_221_; 
lean_dec(v_h__2_217_);
v_val_220_ = lean_ctor_get(v_x_215_, 0);
lean_inc(v_val_220_);
lean_dec_ref(v_x_215_);
v___x_221_ = lean_apply_1(v_h__1_216_, v_val_220_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerExp_match__3_splitter___redArg(lean_object* v_x_222_, lean_object* v_x_223_, lean_object* v_h__1_224_, lean_object* v_h__2_225_){
_start:
{
if (lean_obj_tag(v_x_222_) == 1)
{
if (lean_obj_tag(v_x_223_) == 1)
{
lean_object* v_val_226_; lean_object* v_val_227_; lean_object* v___x_228_; 
lean_dec(v_h__2_225_);
v_val_226_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_val_226_);
lean_dec_ref(v_x_222_);
v_val_227_ = lean_ctor_get(v_x_223_, 0);
lean_inc(v_val_227_);
lean_dec_ref(v_x_223_);
v___x_228_ = lean_apply_2(v_h__1_224_, v_val_226_, v_val_227_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; 
lean_dec(v_h__1_224_);
v___x_229_ = lean_apply_3(v_h__2_225_, v_x_222_, v_x_223_, lean_box(0));
return v___x_229_;
}
}
else
{
lean_object* v___x_230_; 
lean_dec(v_h__1_224_);
v___x_230_ = lean_apply_3(v_h__2_225_, v_x_222_, v_x_223_, lean_box(0));
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerExp_match__3_splitter(lean_object* v_motive_231_, lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_h__1_234_, lean_object* v_h__2_235_){
_start:
{
if (lean_obj_tag(v_x_232_) == 1)
{
if (lean_obj_tag(v_x_233_) == 1)
{
lean_object* v_val_236_; lean_object* v_val_237_; lean_object* v___x_238_; 
lean_dec(v_h__2_235_);
v_val_236_ = lean_ctor_get(v_x_232_, 0);
lean_inc(v_val_236_);
lean_dec_ref(v_x_232_);
v_val_237_ = lean_ctor_get(v_x_233_, 0);
lean_inc(v_val_237_);
lean_dec_ref(v_x_233_);
v___x_238_ = lean_apply_2(v_h__1_234_, v_val_236_, v_val_237_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; 
lean_dec(v_h__1_234_);
v___x_239_ = lean_apply_3(v_h__2_235_, v_x_232_, v_x_233_, lean_box(0));
return v___x_239_;
}
}
else
{
lean_object* v___x_240_; 
lean_dec(v_h__1_234_);
v___x_240_ = lean_apply_3(v_h__2_235_, v_x_232_, v_x_233_, lean_box(0));
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmt1_match__3_splitter___redArg(lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_){
_start:
{
if (lean_obj_tag(v_x_241_) == 1)
{
if (lean_obj_tag(v_x_242_) == 1)
{
if (lean_obj_tag(v_x_243_) == 1)
{
lean_object* v_val_246_; lean_object* v_val_247_; lean_object* v_val_248_; lean_object* v___x_249_; 
lean_dec(v_h__2_245_);
v_val_246_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_val_246_);
lean_dec_ref(v_x_241_);
v_val_247_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_val_247_);
lean_dec_ref(v_x_242_);
v_val_248_ = lean_ctor_get(v_x_243_, 0);
lean_inc(v_val_248_);
lean_dec_ref(v_x_243_);
v___x_249_ = lean_apply_3(v_h__1_244_, v_val_246_, v_val_247_, v_val_248_);
return v___x_249_;
}
else
{
lean_object* v___x_250_; 
lean_dec(v_h__1_244_);
v___x_250_ = lean_apply_4(v_h__2_245_, v_x_241_, v_x_242_, v_x_243_, lean_box(0));
return v___x_250_;
}
}
else
{
lean_object* v___x_251_; 
lean_dec(v_h__1_244_);
v___x_251_ = lean_apply_4(v_h__2_245_, v_x_241_, v_x_242_, v_x_243_, lean_box(0));
return v___x_251_;
}
}
else
{
lean_object* v___x_252_; 
lean_dec(v_h__1_244_);
v___x_252_ = lean_apply_4(v_h__2_245_, v_x_241_, v_x_242_, v_x_243_, lean_box(0));
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmt1_match__3_splitter(lean_object* v_motive_253_, lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_h__1_257_, lean_object* v_h__2_258_){
_start:
{
if (lean_obj_tag(v_x_254_) == 1)
{
if (lean_obj_tag(v_x_255_) == 1)
{
if (lean_obj_tag(v_x_256_) == 1)
{
lean_object* v_val_259_; lean_object* v_val_260_; lean_object* v_val_261_; lean_object* v___x_262_; 
lean_dec(v_h__2_258_);
v_val_259_ = lean_ctor_get(v_x_254_, 0);
lean_inc(v_val_259_);
lean_dec_ref(v_x_254_);
v_val_260_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_val_260_);
lean_dec_ref(v_x_255_);
v_val_261_ = lean_ctor_get(v_x_256_, 0);
lean_inc(v_val_261_);
lean_dec_ref(v_x_256_);
v___x_262_ = lean_apply_3(v_h__1_257_, v_val_259_, v_val_260_, v_val_261_);
return v___x_262_;
}
else
{
lean_object* v___x_263_; 
lean_dec(v_h__1_257_);
v___x_263_ = lean_apply_4(v_h__2_258_, v_x_254_, v_x_255_, v_x_256_, lean_box(0));
return v___x_263_;
}
}
else
{
lean_object* v___x_264_; 
lean_dec(v_h__1_257_);
v___x_264_ = lean_apply_4(v_h__2_258_, v_x_254_, v_x_255_, v_x_256_, lean_box(0));
return v___x_264_;
}
}
else
{
lean_object* v___x_265_; 
lean_dec(v_h__1_257_);
v___x_265_ = lean_apply_4(v_h__2_258_, v_x_254_, v_x_255_, v_x_256_, lean_box(0));
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmtsFold_match__1_splitter___redArg(lean_object* v_x_266_, lean_object* v_x_267_, lean_object* v_h__1_268_, lean_object* v_h__2_269_){
_start:
{
if (lean_obj_tag(v_x_266_) == 1)
{
if (lean_obj_tag(v_x_267_) == 1)
{
lean_object* v_val_270_; lean_object* v_val_271_; lean_object* v___x_272_; 
lean_dec(v_h__2_269_);
v_val_270_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_val_270_);
lean_dec_ref(v_x_266_);
v_val_271_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_val_271_);
lean_dec_ref(v_x_267_);
v___x_272_ = lean_apply_2(v_h__1_268_, v_val_270_, v_val_271_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; 
lean_dec(v_h__1_268_);
v___x_273_ = lean_apply_3(v_h__2_269_, v_x_266_, v_x_267_, lean_box(0));
return v___x_273_;
}
}
else
{
lean_object* v___x_274_; 
lean_dec(v_h__1_268_);
v___x_274_ = lean_apply_3(v_h__2_269_, v_x_266_, v_x_267_, lean_box(0));
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmtsFold_match__1_splitter(lean_object* v_motive_275_, lean_object* v_x_276_, lean_object* v_x_277_, lean_object* v_h__1_278_, lean_object* v_h__2_279_){
_start:
{
if (lean_obj_tag(v_x_276_) == 1)
{
if (lean_obj_tag(v_x_277_) == 1)
{
lean_object* v_val_280_; lean_object* v_val_281_; lean_object* v___x_282_; 
lean_dec(v_h__2_279_);
v_val_280_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_val_280_);
lean_dec_ref(v_x_276_);
v_val_281_ = lean_ctor_get(v_x_277_, 0);
lean_inc(v_val_281_);
lean_dec_ref(v_x_277_);
v___x_282_ = lean_apply_2(v_h__1_278_, v_val_280_, v_val_281_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; 
lean_dec(v_h__1_278_);
v___x_283_ = lean_apply_3(v_h__2_279_, v_x_276_, v_x_277_, lean_box(0));
return v___x_283_;
}
}
else
{
lean_object* v___x_284_; 
lean_dec(v_h__1_278_);
v___x_284_ = lean_apply_3(v_h__2_279_, v_x_276_, v_x_277_, lean_box(0));
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmt1_match__5_splitter___redArg(lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_h__1_287_, lean_object* v_h__2_288_){
_start:
{
if (lean_obj_tag(v_x_285_) == 1)
{
if (lean_obj_tag(v_x_286_) == 1)
{
lean_object* v_val_289_; lean_object* v_val_290_; lean_object* v___x_291_; 
lean_dec(v_h__2_288_);
v_val_289_ = lean_ctor_get(v_x_285_, 0);
lean_inc(v_val_289_);
lean_dec_ref(v_x_285_);
v_val_290_ = lean_ctor_get(v_x_286_, 0);
lean_inc(v_val_290_);
lean_dec_ref(v_x_286_);
v___x_291_ = lean_apply_2(v_h__1_287_, v_val_289_, v_val_290_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; 
lean_dec(v_h__1_287_);
v___x_292_ = lean_apply_3(v_h__2_288_, v_x_285_, v_x_286_, lean_box(0));
return v___x_292_;
}
}
else
{
lean_object* v___x_293_; 
lean_dec(v_h__1_287_);
v___x_293_ = lean_apply_3(v_h__2_288_, v_x_285_, v_x_286_, lean_box(0));
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler___private_Pancake_ServeExportServes_0__Pancake_Lower_lowerStmt1_match__5_splitter(lean_object* v_motive_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_h__1_297_, lean_object* v_h__2_298_){
_start:
{
if (lean_obj_tag(v_x_295_) == 1)
{
if (lean_obj_tag(v_x_296_) == 1)
{
lean_object* v_val_299_; lean_object* v_val_300_; lean_object* v___x_301_; 
lean_dec(v_h__2_298_);
v_val_299_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_val_299_);
lean_dec_ref(v_x_295_);
v_val_300_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_val_300_);
lean_dec_ref(v_x_296_);
v___x_301_ = lean_apply_2(v_h__1_297_, v_val_299_, v_val_300_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
lean_dec(v_h__1_297_);
v___x_302_ = lean_apply_3(v_h__2_298_, v_x_295_, v_x_296_, lean_box(0));
return v___x_302_;
}
}
else
{
lean_object* v___x_303_; 
lean_dec(v_h__1_297_);
v___x_303_ = lean_apply_3(v_h__2_298_, v_x_295_, v_x_296_, lean_box(0));
return v___x_303_;
}
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__0(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lp_orb_x2dcompiler_Pancake_ServeSlice_resp200;
v___x_305_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__1(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__0, &lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__0);
v___x_307_ = lp_orb_x2dcompiler_Pancake_ServeEmit_bytesOf(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200(void){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__1, &lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200___closed__1);
return v___x_308_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__0(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lp_orb_x2dcompiler_Pancake_ServeSlice_resp405;
v___x_310_ = lp_orb_x2dcompiler_Pancake_SerializeCompile_serialize(v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__1(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__0, &lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__0_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__0);
v___x_312_ = lp_orb_x2dcompiler_Pancake_ServeEmit_bytesOf(v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405(void){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__1, &lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405___closed__1);
return v___x_313_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_LowerBridgeSem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_ServeExportServes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_LowerBridgeSem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel = _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ServeExportServes_decodeModel);
lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200 = _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ServeExportServes_BS200);
lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405 = _init_lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_ServeExportServes_BS405);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
