// Lean compiler output
// Module: Pancake.StageLift2Cond
// Imports: public import Init public meta import Init public import Pancake.StageLift2Inst
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampFnR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampProgR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR___lam__0___boxed(lean_object*);
static const lean_closure_object lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR___closed__0_value;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Warning"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Link"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Cache-Control"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Expires"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Last-Modified"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Retry-After"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName;
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Content-Location"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName___closed__1;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningSpecR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkSpecR(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_cacheControlDec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_cacheControlDec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_cacheControlSpecR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresSpecR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_immutableSpecR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_contentLocationSpecR(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_lastModifiedDec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_lastModifiedDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_lastModifiedSpecR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterSpecR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_statusStampS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_staticStatusStampS(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Internal Server Error"};
static const lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__0 = (const lean_object*)&lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__0_value;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__1;
static lean_once_cell_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__2;
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500;
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_statusStampSpecR___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_statusStampSpecR___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_statusStampSpecR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampFnR(lean_object* v_c_1_, lean_object* v_name_2_, lean_object* v_val_3_, lean_object* v_ctx_4_, lean_object* v_r_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
lean_inc_ref(v_r_5_);
v___x_6_ = lean_apply_2(v_c_1_, v_ctx_4_, v_r_5_);
v___x_7_ = lean_unbox(v___x_6_);
if (v___x_7_ == 0)
{
lean_dec(v_val_3_);
lean_dec(v_name_2_);
return v_r_5_;
}
else
{
lean_object* v_status_8_; lean_object* v_reason_9_; lean_object* v_headers_10_; lean_object* v_body_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_22_; 
v_status_8_ = lean_ctor_get(v_r_5_, 0);
v_reason_9_ = lean_ctor_get(v_r_5_, 1);
v_headers_10_ = lean_ctor_get(v_r_5_, 2);
v_body_11_ = lean_ctor_get(v_r_5_, 3);
v_isSharedCheck_22_ = !lean_is_exclusive(v_r_5_);
if (v_isSharedCheck_22_ == 0)
{
v___x_13_ = v_r_5_;
v_isShared_14_ = v_isSharedCheck_22_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_body_11_);
lean_inc(v_headers_10_);
lean_inc(v_reason_9_);
lean_inc(v_status_8_);
lean_dec(v_r_5_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_22_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_2_);
lean_ctor_set(v___x_15_, 1, v_val_3_);
v___x_16_ = lean_box(0);
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_15_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
v___x_18_ = l_List_appendTR___redArg(v_headers_10_, v___x_17_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 2, v___x_18_);
v___x_20_ = v___x_13_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_status_8_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v_reason_9_);
lean_ctor_set(v_reuseFailAlloc_21_, 2, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_21_, 3, v_body_11_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampProgR(lean_object* v_c_23_, lean_object* v_name_24_, lean_object* v_val_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_26_, 0, v_name_24_);
lean_ctor_set(v___x_26_, 1, v_val_25_);
v___x_27_ = lean_box(0);
v___x_28_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_28_, 0, v_c_23_);
lean_ctor_set(v___x_28_, 1, v___x_26_);
lean_ctor_set(v___x_28_, 2, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR___lam__0(lean_object* v_x_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = 0;
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR___lam__0___boxed(lean_object* v_x_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR___lam__0(v_x_31_);
lean_dec_ref(v_x_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR(lean_object* v_c_35_, lean_object* v_name_36_, lean_object* v_val_37_){
_start:
{
lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___f_38_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR___closed__0));
v___x_39_ = lean_box(0);
v___x_40_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampProgR(v_c_35_, v_name_36_, v_val_37_);
v___x_41_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_41_, 0, v___f_38_);
lean_ctor_set(v___x_41_, 1, v___x_39_);
lean_ctor_set(v___x_41_, 2, v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName___closed__1(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName___closed__0));
v___x_44_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName___closed__1);
return v___x_45_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName___closed__1(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName___closed__0));
v___x_48_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName___closed__1);
return v___x_49_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName___closed__1(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName___closed__0));
v___x_52_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName(void){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName___closed__1);
return v___x_53_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName___closed__1(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName___closed__0));
v___x_56_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName___closed__1);
return v___x_57_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName___closed__1(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName___closed__0));
v___x_60_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName(void){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName___closed__1);
return v___x_61_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName___closed__1(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName___closed__0));
v___x_64_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName___closed__1);
return v___x_65_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName___closed__1(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName___closed__0));
v___x_68_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName(void){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName___closed__1);
return v___x_69_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec___redArg(lean_object* v_isTransformed_70_, lean_object* v_hasWarning_71_, lean_object* v_r_72_){
_start:
{
lean_object* v_headers_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v_headers_73_ = lean_ctor_get(v_r_72_, 2);
lean_inc_n(v_headers_73_, 2);
lean_dec_ref(v_r_72_);
v___x_74_ = lean_apply_1(v_isTransformed_70_, v_headers_73_);
v___x_75_ = lean_unbox(v___x_74_);
if (v___x_75_ == 0)
{
uint8_t v___x_76_; 
lean_dec(v_headers_73_);
lean_dec_ref(v_hasWarning_71_);
v___x_76_ = lean_unbox(v___x_74_);
return v___x_76_;
}
else
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_apply_1(v_hasWarning_71_, v_headers_73_);
v___x_78_ = lean_unbox(v___x_77_);
if (v___x_78_ == 0)
{
uint8_t v___x_79_; 
v___x_79_ = lean_unbox(v___x_74_);
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec___redArg___boxed(lean_object* v_isTransformed_81_, lean_object* v_hasWarning_82_, lean_object* v_r_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec___redArg(v_isTransformed_81_, v_hasWarning_82_, v_r_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec(lean_object* v_isTransformed_86_, lean_object* v_hasWarning_87_, lean_object* v_x_88_, lean_object* v_r_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec___redArg(v_isTransformed_86_, v_hasWarning_87_, v_r_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec___boxed(lean_object* v_isTransformed_91_, lean_object* v_hasWarning_92_, lean_object* v_x_93_, lean_object* v_r_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec(v_isTransformed_91_, v_hasWarning_92_, v_x_93_, v_r_94_);
lean_dec_ref(v_x_93_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningSpecR(lean_object* v_isTransformed_97_, lean_object* v_hasWarning_98_, lean_object* v_val_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_warningDec___boxed), 4, 2);
lean_closure_set(v___x_100_, 0, v_isTransformed_97_);
lean_closure_set(v___x_100_, 1, v_hasWarning_98_);
v___x_101_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName;
v___x_102_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR(v___x_100_, v___x_101_, v_val_99_);
return v___x_102_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec___redArg(lean_object* v_hasLink_103_, lean_object* v_r_104_){
_start:
{
lean_object* v_status_105_; lean_object* v_headers_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_status_105_ = lean_ctor_get(v_r_104_, 0);
lean_inc(v_status_105_);
v_headers_106_ = lean_ctor_get(v_r_104_, 2);
lean_inc(v_headers_106_);
lean_dec_ref(v_r_104_);
v___x_107_ = lean_unsigned_to_nat(200u);
v___x_108_ = lean_nat_dec_eq(v_status_105_, v___x_107_);
lean_dec(v_status_105_);
if (v___x_108_ == 0)
{
lean_dec(v_headers_106_);
lean_dec_ref(v_hasLink_103_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_apply_1(v_hasLink_103_, v_headers_106_);
v___x_110_ = lean_unbox(v___x_109_);
if (v___x_110_ == 0)
{
return v___x_108_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec___redArg___boxed(lean_object* v_hasLink_112_, lean_object* v_r_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec___redArg(v_hasLink_112_, v_r_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec(lean_object* v_hasLink_116_, lean_object* v_x_117_, lean_object* v_r_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec___redArg(v_hasLink_116_, v_r_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec___boxed(lean_object* v_hasLink_120_, lean_object* v_x_121_, lean_object* v_r_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec(v_hasLink_120_, v_x_121_, v_r_122_);
lean_dec_ref(v_x_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkSpecR(lean_object* v_hasLink_125_, lean_object* v_val_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkDec___boxed), 3, 1);
lean_closure_set(v___x_127_, 0, v_hasLink_125_);
v___x_128_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName;
v___x_129_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR(v___x_127_, v___x_128_, v_val_126_);
return v___x_129_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_cacheControlDec(lean_object* v_isStaticGet_130_, lean_object* v_c_131_, lean_object* v_r_132_){
_start:
{
lean_object* v_status_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_status_133_ = lean_ctor_get(v_r_132_, 0);
v___x_134_ = lean_unsigned_to_nat(200u);
v___x_135_ = lean_nat_dec_eq(v_status_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_dec_ref(v_c_131_);
lean_dec_ref(v_isStaticGet_130_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_apply_1(v_isStaticGet_130_, v_c_131_);
v___x_137_ = lean_unbox(v___x_136_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_cacheControlDec___boxed(lean_object* v_isStaticGet_138_, lean_object* v_c_139_, lean_object* v_r_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_cacheControlDec(v_isStaticGet_138_, v_c_139_, v_r_140_);
lean_dec_ref(v_r_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_cacheControlSpecR(lean_object* v_isStaticGet_143_, lean_object* v_val_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_cacheControlDec___boxed), 3, 1);
lean_closure_set(v___x_145_, 0, v_isStaticGet_143_);
v___x_146_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName;
v___x_147_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR(v___x_145_, v___x_146_, v_val_144_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresSpecR(lean_object* v_isStaticGet_148_, lean_object* v_val_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_cacheControlDec___boxed), 3, 1);
lean_closure_set(v___x_150_, 0, v_isStaticGet_148_);
v___x_151_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName;
v___x_152_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR(v___x_150_, v___x_151_, v_val_149_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_immutableSpecR(lean_object* v_isStaticGet_153_, lean_object* v_val_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_cacheControlDec___boxed), 3, 1);
lean_closure_set(v___x_155_, 0, v_isStaticGet_153_);
v___x_156_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName;
v___x_157_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR(v___x_155_, v___x_156_, v_val_154_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_contentLocationSpecR(lean_object* v_isStaticGet_158_, lean_object* v_val_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_cacheControlDec___boxed), 3, 1);
lean_closure_set(v___x_160_, 0, v_isStaticGet_158_);
v___x_161_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName;
v___x_162_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR(v___x_160_, v___x_161_, v_val_159_);
return v___x_162_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_lastModifiedDec(lean_object* v_isStaticGet_163_, lean_object* v_hasLm_164_, lean_object* v_c_165_, lean_object* v_r_166_){
_start:
{
lean_object* v_status_167_; lean_object* v_headers_168_; uint8_t v___y_170_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_status_167_ = lean_ctor_get(v_r_166_, 0);
lean_inc(v_status_167_);
v_headers_168_ = lean_ctor_get(v_r_166_, 2);
lean_inc(v_headers_168_);
lean_dec_ref(v_r_166_);
v___x_174_ = lean_unsigned_to_nat(200u);
v___x_175_ = lean_nat_dec_eq(v_status_167_, v___x_174_);
lean_dec(v_status_167_);
if (v___x_175_ == 0)
{
lean_dec_ref(v_c_165_);
lean_dec_ref(v_isStaticGet_163_);
v___y_170_ = v___x_175_;
goto v___jp_169_;
}
else
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_apply_1(v_isStaticGet_163_, v_c_165_);
v___x_177_ = lean_unbox(v___x_176_);
v___y_170_ = v___x_177_;
goto v___jp_169_;
}
v___jp_169_:
{
if (v___y_170_ == 0)
{
lean_dec(v_headers_168_);
lean_dec_ref(v_hasLm_164_);
return v___y_170_;
}
else
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_apply_1(v_hasLm_164_, v_headers_168_);
v___x_172_ = lean_unbox(v___x_171_);
if (v___x_172_ == 0)
{
return v___y_170_;
}
else
{
uint8_t v___x_173_; 
v___x_173_ = 0;
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_lastModifiedDec___boxed(lean_object* v_isStaticGet_178_, lean_object* v_hasLm_179_, lean_object* v_c_180_, lean_object* v_r_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_lastModifiedDec(v_isStaticGet_178_, v_hasLm_179_, v_c_180_, v_r_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_lastModifiedSpecR(lean_object* v_isStaticGet_184_, lean_object* v_hasLm_185_, lean_object* v_val_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_lastModifiedDec___boxed), 4, 2);
lean_closure_set(v___x_187_, 0, v_isStaticGet_184_);
lean_closure_set(v___x_187_, 1, v_hasLm_185_);
v___x_188_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName;
v___x_189_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR(v___x_187_, v___x_188_, v_val_186_);
return v___x_189_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec___redArg(lean_object* v_needsRetryAfter_190_, lean_object* v_r_191_){
_start:
{
lean_object* v_status_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_status_192_ = lean_ctor_get(v_r_191_, 0);
lean_inc(v_status_192_);
lean_dec_ref(v_r_191_);
v___x_193_ = lean_apply_1(v_needsRetryAfter_190_, v_status_192_);
v___x_194_ = lean_unbox(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec___redArg___boxed(lean_object* v_needsRetryAfter_195_, lean_object* v_r_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec___redArg(v_needsRetryAfter_195_, v_r_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec(lean_object* v_needsRetryAfter_199_, lean_object* v_x_200_, lean_object* v_r_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec___redArg(v_needsRetryAfter_199_, v_r_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec___boxed(lean_object* v_needsRetryAfter_203_, lean_object* v_x_204_, lean_object* v_r_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec(v_needsRetryAfter_203_, v_x_204_, v_r_205_);
lean_dec_ref(v_x_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterSpecR(lean_object* v_needsRetryAfter_208_, lean_object* v_val_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryAfterDec___boxed), 3, 1);
lean_closure_set(v___x_210_, 0, v_needsRetryAfter_208_);
v___x_211_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName;
v___x_212_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR(v___x_210_, v___x_211_, v_val_209_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_statusStampS(lean_object* v_k_213_, lean_object* v_name_214_, lean_object* v_val_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_216_, 0, v_name_214_);
lean_ctor_set(v___x_216_, 1, v_val_215_);
v___x_217_ = lean_box(0);
v___x_218_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_218_, 0, v_k_213_);
lean_ctor_set(v___x_218_, 1, v___x_216_);
lean_ctor_set(v___x_218_, 2, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_staticStatusStampS(lean_object* v_d_219_, lean_object* v_name_220_, lean_object* v_val_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = lean_unsigned_to_nat(200u);
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v_name_220_);
lean_ctor_set(v___x_223_, 1, v_val_221_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_225_, 0, v_d_219_);
lean_ctor_set(v___x_225_, 1, v___x_223_);
lean_ctor_set(v___x_225_, 2, v___x_224_);
v___x_226_ = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(v___x_226_, 0, v___x_222_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
lean_ctor_set(v___x_226_, 2, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__1(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__0));
v___x_229_ = lp_orb_x2dcompiler_Pancake_StageProg_str(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__2(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_230_ = lean_box(0);
v___x_231_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__1, &lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__1_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__1);
v___x_232_ = lean_unsigned_to_nat(500u);
v___x_233_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_231_);
lean_ctor_set(v___x_233_, 2, v___x_230_);
lean_ctor_set(v___x_233_, 3, v___x_230_);
return v___x_233_;
}
}
static lean_object* _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__2, &lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__2_once, _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500___closed__2);
return v___x_234_;
}
}
LEAN_EXPORT uint8_t lp_orb_x2dcompiler_Pancake_StageLift2Cond_statusStampSpecR___lam__0(lean_object* v_k_235_, lean_object* v_x_236_, lean_object* v_r_237_){
_start:
{
lean_object* v_status_238_; uint8_t v___x_239_; 
v_status_238_ = lean_ctor_get(v_r_237_, 0);
v___x_239_ = lean_nat_dec_eq(v_status_238_, v_k_235_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_statusStampSpecR___lam__0___boxed(lean_object* v_k_240_, lean_object* v_x_241_, lean_object* v_r_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_statusStampSpecR___lam__0(v_k_240_, v_x_241_, v_r_242_);
lean_dec_ref(v_r_242_);
lean_dec_ref(v_x_241_);
lean_dec(v_k_240_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* lp_orb_x2dcompiler_Pancake_StageLift2Cond_statusStampSpecR(lean_object* v_k_245_, lean_object* v_name_246_, lean_object* v_val_247_){
_start:
{
lean_object* v___f_248_; lean_object* v___x_249_; 
v___f_248_ = lean_alloc_closure((void*)(lp_orb_x2dcompiler_Pancake_StageLift2Cond_statusStampSpecR___lam__0___boxed), 3, 1);
lean_closure_set(v___f_248_, 0, v_k_245_);
v___x_249_ = lp_orb_x2dcompiler_Pancake_StageLift2Cond_stampSpecR(v___f_248_, v_name_246_, v_val_247_);
return v___x_249_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_orb_x2dcompiler_Pancake_StageLift2Inst(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_orb_x2dcompiler_Pancake_StageLift2Cond(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_orb_x2dcompiler_Pancake_StageLift2Inst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Cond_warnName);
lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Cond_linkName);
lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Cond_ccName);
lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Cond_expiresName);
lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Cond_lmName);
lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Cond_retryName);
lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName = _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Cond_clocName);
lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500 = _init_lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500();
lean_mark_persistent(lp_orb_x2dcompiler_Pancake_StageLift2Cond_resp500);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
