// Lean compiler output
// Module: LeanProofs.L008_Finitude_2
// Imports: Init Mathlib.Data.Fintype.Basic Mathlib.Data.Finset.Basic Mathlib.Data.Nat.Basic Mathlib.Data.Real.Basic Mathlib.Logic.Basic
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
static lean_object* l_LogicalMechanics_logical__state__bound___closed__0;
LEAN_EXPORT lean_object* l_LogicalMechanics_logical__state__bound;
static lean_object* _init_l_LogicalMechanics_logical__state__bound___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000");
return x_1;
}
}
static lean_object* _init_l_LogicalMechanics_logical__state__bound() {
_start:
{
lean_object* x_1; 
x_1 = l_LogicalMechanics_logical__state__bound___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Logic_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanProofs_L008__Finitude__2(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Logic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_LogicalMechanics_logical__state__bound___closed__0 = _init_l_LogicalMechanics_logical__state__bound___closed__0();
lean_mark_persistent(l_LogicalMechanics_logical__state__bound___closed__0);
l_LogicalMechanics_logical__state__bound = _init_l_LogicalMechanics_logical__state__bound();
lean_mark_persistent(l_LogicalMechanics_logical__state__bound);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
