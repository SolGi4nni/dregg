// Lean compiler output
// Module: Pancake.FullResponseCompile
// Imports: public import Init public meta import Init public import Pancake.ByteCopy public import Pancake.ModelUnify public import Pancake.StructEmit
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
extern lean_object* lp_orb_x2dcompiler_Pancake_StructEmit_resp404;
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_writeByteArray(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_SerializeStruct_headBytes(lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_ModelUnify_byteLit(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
lean_object* lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_fullRespLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_fullRespLit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__0_value;
static const lean_closure_object lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(64) << 1) | 1))} };
static const lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__0_value;
static const lean_closure_object lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__1 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__1_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_fullRespLit(lean_object* v_resp_1_, lean_object* v_obase_2_, lean_object* v_src_3_){
_start:
{
lean_object* v_body_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_body_4_ = lean_ctor_get(v_resp_1_, 3);
v___x_5_ = lp_orb_x2dcompiler_Pancake_SerializeStruct_headBytes(v_resp_1_);
lean_inc(v___x_5_);
v___x_6_ = lp_orb_x2dcompiler_Pancake_ModelUnify_byteLit(v_obase_2_, v___x_5_);
v___x_7_ = lean_unsigned_to_nat(64u);
v___x_8_ = l_List_lengthTR___redArg(v___x_5_);
lean_dec(v___x_5_);
v___x_9_ = l_BitVec_ofNat(v___x_7_, v___x_8_);
lean_dec(v___x_8_);
v___x_10_ = l_BitVec_add(v___x_7_, v_obase_2_, v___x_9_);
lean_dec(v___x_9_);
v___x_11_ = l_List_lengthTR___redArg(v_body_4_);
v___x_12_ = lp_orb_x2dcompiler_Pancake_ByteCopy_copySeg(v___x_10_, v_src_3_, v___x_11_);
lean_dec(v___x_11_);
v___x_13_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_6_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_fullRespLit___boxed(lean_object* v_resp_14_, lean_object* v_obase_15_, lean_object* v_src_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_orb_x2dcompiler_Pancake_FullResponseCompile_fullRespLit(v_resp_14_, v_obase_15_, v_src_16_);
lean_dec(v_obase_15_);
lean_dec_ref(v_resp_14_);
return v_res_17_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__0(lean_object* v_x_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = 1;
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__0___boxed(lean_object* v_x_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__0(v_x_20_);
lean_dec(v_x_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__1(lean_object* v___x_23_, lean_object* v_x_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = l_BitVec_ofNat(v___x_23_, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__1___boxed(lean_object* v___x_27_, lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___lam__1(v___x_27_, v_x_28_);
lean_dec(v_x_28_);
lean_dec(v___x_27_);
return v_res_29_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__2(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_unsigned_to_nat(1024u);
v___x_34_ = lean_unsigned_to_nat(64u);
v___x_35_ = l_BitVec_ofNat(v___x_34_, v___x_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR(lean_object* v_a_36_){
_start:
{
lean_object* v___x_37_; lean_object* v_body_38_; lean_object* v___f_39_; uint8_t v___x_40_; lean_object* v___f_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_37_ = lp_orb_x2dcompiler_Pancake_StructEmit_resp404;
v_body_38_ = lean_ctor_get(v___x_37_, 3);
v___f_39_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__0));
v___x_40_ = 0;
v___f_41_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__1));
v___x_42_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__2, &lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__2);
lean_inc(v_body_38_);
v___x_43_ = lp_orb_x2dcompiler_Pancake_writeByteArray(v___f_39_, v___x_40_, v___x_42_, v_body_38_, v___f_41_, v_a_36_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___lam__0(lean_object* v_x_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___lam__0___boxed(lean_object* v_x_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___lam__0(v_x_46_);
lean_dec_ref(v_x_46_);
return v_res_47_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_unsigned_to_nat(64u);
v___x_52_ = l_BitVec_ofNat(v___x_51_, v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg(lean_object* v_f_53_){
_start:
{
lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___f_54_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__0));
v___f_55_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_FullResponseCompile_wmemFR___closed__0));
v___x_56_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__1));
v___x_57_ = 0;
v___x_58_ = lean_unsigned_to_nat(100u);
v___x_59_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__2, &lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg___closed__2);
v___x_60_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_60_, 0, v___f_54_);
lean_ctor_set(v___x_60_, 1, v___x_56_);
lean_ctor_set(v___x_60_, 2, v___f_55_);
lean_ctor_set(v___x_60_, 3, v___x_58_);
lean_ctor_set(v___x_60_, 4, v_f_53_);
lean_ctor_set(v___x_60_, 5, v___x_59_);
lean_ctor_set_uint8(v___x_60_, sizeof(void*)*6, v___x_57_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR(lean_object* v_00_u03c3_61_, lean_object* v_f_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_orb_x2dcompiler_Pancake_FullResponseCompile_wstateFR___redArg(v_f_62_);
return v___x_63_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_ByteCopy(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_ModelUnify(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_StructEmit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_FullResponseCompile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_ByteCopy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_ModelUnify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_StructEmit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
