// Copyright 2014 the V8 project authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#include "src/builtins/accessors.h"
#include "src/codegen/compiler.h"
#include "src/execution/arguments-inl.h"
#include "src/execution/isolate-inl.h"
#include "src/heap/heap-inl.h"  // For ToBoolean. TODO(jkummerow): Drop.
#include "src/logging/counters.h"
#include "src/runtime/runtime-utils.h"
#include "src/taint_tracking/symbolic_state.h"

namespace v8 {
namespace internal {

// TODO(5530): Remove once uses in debug.js are gone.
RUNTIME_FUNCTION(Runtime_FunctionGetScriptSource) {
  HandleScope scope(isolate);
  DCHECK_EQ(1, args.length());
  CONVERT_ARG_HANDLE_CHECKED(JSReceiver, function, 0);

  if (function->IsJSFunction()) {
    Handle<Object> script(Handle<JSFunction>::cast(function)->shared().script(),
                          isolate);
    if (script->IsScript()) return Handle<Script>::cast(script)->source();
  }
  return ReadOnlyRoots(isolate).undefined_value();
}

RUNTIME_FUNCTION(Runtime_FunctionGetScriptId) {
  HandleScope scope(isolate);
  DCHECK_EQ(1, args.length());
  CONVERT_ARG_HANDLE_CHECKED(JSReceiver, function, 0);

  if (function->IsJSFunction()) {
    Handle<Object> script(Handle<JSFunction>::cast(function)->shared().script(),
                          isolate);
    if (script->IsScript()) {
      return Smi::FromInt(Handle<Script>::cast(script)->id());
    }
  }
  return Smi::FromInt(-1);
}

RUNTIME_FUNCTION(Runtime_FunctionGetSourceCode) {
  HandleScope scope(isolate);
  DCHECK_EQ(1, args.length());
  CONVERT_ARG_HANDLE_CHECKED(JSReceiver, function, 0);
  if (function->IsJSFunction()) {
    Handle<SharedFunctionInfo> shared(
        Handle<JSFunction>::cast(function)->shared(), isolate);
    return *SharedFunctionInfo::GetSourceCode(shared);
  }
  return ReadOnlyRoots(isolate).undefined_value();
}


RUNTIME_FUNCTION(Runtime_FunctionGetScriptSourcePosition) {
  SealHandleScope shs(isolate);
  DCHECK_EQ(1, args.length());

  CONVERT_ARG_CHECKED(JSFunction, fun, 0);
  int pos = fun.shared().StartPosition();
  return Smi::FromInt(pos);
}


RUNTIME_FUNCTION(Runtime_FunctionIsAPIFunction) {
  SealHandleScope shs(isolate);
  DCHECK_EQ(1, args.length());

  CONVERT_ARG_CHECKED(JSFunction, f, 0);
  return isolate->heap()->ToBoolean(f.shared().IsApiFunction());
}


RUNTIME_FUNCTION(Runtime_Call) {
  HandleScope scope(isolate);
  DCHECK_LE(2, args.length());
  int const argc = args.length() - 2;
  CONVERT_ARG_HANDLE_CHECKED(Object, target, 0);
  CONVERT_ARG_HANDLE_CHECKED(Object, receiver, 1);
  ScopedVector<Handle<Object>> argv(argc);
  for (int i = 0; i < argc; ++i) {
    argv[i] = args.at(2 + i);
  }
  RETURN_RESULT_OR_FAILURE(
      isolate, Execution::Call(isolate, target, receiver, argc, argv.begin()));
}


RUNTIME_FUNCTION(Runtime_IsFunction) {
  SealHandleScope shs(isolate);
  DCHECK_EQ(1, args.length());
  CONVERT_ARG_CHECKED(Object, object, 0);
  return isolate->heap()->ToBoolean(object.IsFunction());
}

RUNTIME_FUNCTION(Runtime_ShouldPrintUndefinedProperties){
  HandleScope scope(isolate);
  DCHECK_EQ(0, args.length());

  if (FLAG_print_undefined_properties) {
    return isolate->heap()->ToBoolean(true);
  }else{
    return isolate->heap()->ToBoolean(false);
  }
}

RUNTIME_FUNCTION(Runtime_ShouldGenerateProperties){
  HandleScope scope(isolate);
  DCHECK_EQ(0, args.length());

  if (FLAG_generate_undefined_properties) {
    return isolate->heap()->ToBoolean(true);
  }else{
    return isolate->heap()->ToBoolean(false);
  }
}


RUNTIME_FUNCTION(Runtime_FakePropertiesEnumerable){
  HandleScope scope(isolate);
  DCHECK_EQ(0, args.length());

  if (FLAG_fake_properties_enumerable) {
    return isolate->heap()->ToBoolean(true);
  }else{
    return isolate->heap()->ToBoolean(false);
  }
}


// add these two to pass fakeKey and fakeValue from runtime flags
RUNTIME_FUNCTION(Runtime_GetFakeKey){
  HandleScope scope(isolate);
  DCHECK_EQ(0, args.length());

  return *(
          isolate->factory()->NewStringFromAsciiChecked(FLAG_undefined_property_fakeKey_string));
}

RUNTIME_FUNCTION(Runtime_GetFakeValue){
  HandleScope scope(isolate);
  DCHECK_EQ(0, args.length());

  return *(
          isolate->factory()->NewStringFromAsciiChecked(FLAG_undefined_property_fakeValue_string));
}

RUNTIME_FUNCTION(Runtime_ObjectDefinePropertyMinnie){
  HandleScope scope(isolate);
  DCHECK_EQ(3, args.length());
  CONVERT_ARG_HANDLE_CHECKED(Object, target, 0);
  CONVERT_ARG_HANDLE_CHECKED(Object, key, 1);
  CONVERT_ARG_HANDLE_CHECKED(Object, attributes, 2);

  return JSReceiver::DefineProperty(isolate, target, key, attributes);

  // return *Handle<Object>::cast(
  //         isolate->factory()->NewStringFromAsciiChecked(FLAG_undefined_property_fakeValue_string));
}


// [Minnie] Exposed concolic entry point (paper III-D). Callable from
// JS as %ConcolicQueryFork(lhs, rhs, op) where op is a number:
//   0 = equality, 1 = prefix, 2 = contains.
// Returns either undefined (nothing to fork / solver unsat / concolic
// support not compiled in) or an array [lhs_assignment, rhs_assignment]
// of concrete strings that would flip the branch.
//
// The bytecode-level hooks in the interpreter (which will call into
// this function automatically for TestEqual / JumpIfTrue) land as a
// follow-up patch; for now tests and the exerciser can invoke this
// through the %ConcolicQueryFork runtime intrinsic.
RUNTIME_FUNCTION(Runtime_ConcolicQueryFork) {
  HandleScope scope(isolate);
  DCHECK_EQ(3, args.length());
  if (!args[0].IsString() || !args[1].IsString()) {
    return ReadOnlyRoots(isolate).undefined_value();
  }
  CONVERT_ARG_HANDLE_CHECKED(String, lhs, 0);
  CONVERT_ARG_HANDLE_CHECKED(String, rhs, 1);
  CONVERT_SMI_ARG_CHECKED(op, 2);
  tainttracking::ForkAssignment fa =
      tainttracking::QueryFork(isolate, lhs, rhs, op);
  if (!fa.available) return ReadOnlyRoots(isolate).undefined_value();
  Handle<FixedArray> arr = isolate->factory()->NewFixedArray(2);
  arr->set(0, *isolate->factory()->NewStringFromUtf8(
                  Vector<const char>(fa.lhs_assignment.data(),
                                     fa.lhs_assignment.size()))
                  .ToHandleChecked());
  arr->set(1, *isolate->factory()->NewStringFromUtf8(
                  Vector<const char>(fa.rhs_assignment.data(),
                                     fa.rhs_assignment.size()))
                  .ToHandleChecked());
  return *isolate->factory()->NewJSArrayWithElements(arr);
}

}  // namespace internal
}  // namespace v8
