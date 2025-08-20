// Lean compiler output
// Module: LeanProofs.L002_Uncertainty_Principle
// Imports: Init Mathlib.Data.Fintype.Basic Mathlib.Data.Fintype.Card Mathlib.Data.Fintype.Prod Mathlib.Data.Fin.Basic Mathlib.Data.Bool.Basic Mathlib.Logic.Basic Mathlib.Algebra.Ring.Basic Mathlib.Tactic.Linarith
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
static lean_object* l_PauliFromLogic_instFintypeProdBool__leanProofs___closed__0;
LEAN_EXPORT lean_object* l_PauliFromLogic_information__content___redArg(lean_object*);
LEAN_EXPORT lean_object* l_PauliFromLogic_max__system__information___redArg___boxed(lean_object*);
extern lean_object* l_Bool_fintype;
LEAN_EXPORT lean_object* l_PauliFromLogic_information__content(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PauliFromLogic_instFintypeProdBool__leanProofs;
lean_object* l_Multiset_card___redArg(lean_object*);
LEAN_EXPORT lean_object* l_PauliFromLogic_max__system__information___boxed(lean_object*, lean_object*);
lean_object* l_Multiset_product___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PauliFromLogic_max__system__information___redArg(lean_object*);
LEAN_EXPORT lean_object* l_PauliFromLogic_max__system__information(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PauliFromLogic_information__content___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PauliFromLogic_information__content___redArg___boxed(lean_object*);
static lean_object* _init_l_PauliFromLogic_instFintypeProdBool__leanProofs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Bool_fintype;
x_2 = l_Multiset_product___redArg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_PauliFromLogic_instFintypeProdBool__leanProofs() {
_start:
{
lean_object* x_1; 
x_1 = l_PauliFromLogic_instFintypeProdBool__leanProofs___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_PauliFromLogic_information__content___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Multiset_card___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PauliFromLogic_information__content(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Multiset_card___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PauliFromLogic_information__content___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PauliFromLogic_information__content___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PauliFromLogic_information__content___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PauliFromLogic_information__content(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PauliFromLogic_max__system__information___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Multiset_card___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PauliFromLogic_max__system__information(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Multiset_card___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PauliFromLogic_max__system__information___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PauliFromLogic_max__system__information___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PauliFromLogic_max__system__information___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PauliFromLogic_max__system__information(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Card(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Prod(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fin_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Bool_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Logic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Ring_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_Linarith(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanProofs_L002__Uncertainty__Principle(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Card(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Prod(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fin_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Bool_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Logic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Ring_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Linarith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PauliFromLogic_instFintypeProdBool__leanProofs___closed__0 = _init_l_PauliFromLogic_instFintypeProdBool__leanProofs___closed__0();
lean_mark_persistent(l_PauliFromLogic_instFintypeProdBool__leanProofs___closed__0);
l_PauliFromLogic_instFintypeProdBool__leanProofs = _init_l_PauliFromLogic_instFintypeProdBool__leanProofs();
lean_mark_persistent(l_PauliFromLogic_instFintypeProdBool__leanProofs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
