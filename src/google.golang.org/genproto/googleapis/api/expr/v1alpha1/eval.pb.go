// Copyright 2020 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Code generated by protoc-gen-go. DO NOT EDIT.
// versions:
// 	protoc-gen-go v1.22.0
// 	protoc        v3.12.3
// source: google/api/expr/v1alpha1/eval.proto

package expr

import (
	reflect "reflect"
	sync "sync"

	proto "github.com/golang/protobuf/proto"
	status "google.golang.org/genproto/googleapis/rpc/status"
	protoreflect "google.golang.org/protobuf/reflect/protoreflect"
	protoimpl "google.golang.org/protobuf/runtime/protoimpl"
)

const (
	// Verify that this generated code is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(20 - protoimpl.MinVersion)
	// Verify that runtime/protoimpl is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(protoimpl.MaxVersion - 20)
)

// This is a compile-time assertion that a sufficiently up-to-date version
// of the legacy proto package is being used.
const _ = proto.ProtoPackageIsVersion4

// The state of an evaluation.
//
// Can represent an inital, partial, or completed state of evaluation.
type EvalState struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// The unique values referenced in this message.
	Values []*ExprValue `protobuf:"bytes,1,rep,name=values,proto3" json:"values,omitempty"`
	// An ordered list of results.
	//
	// Tracks the flow of evaluation through the expression.
	// May be sparse.
	Results []*EvalState_Result `protobuf:"bytes,3,rep,name=results,proto3" json:"results,omitempty"`
}

func (x *EvalState) Reset() {
	*x = EvalState{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_api_expr_v1alpha1_eval_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *EvalState) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*EvalState) ProtoMessage() {}

func (x *EvalState) ProtoReflect() protoreflect.Message {
	mi := &file_google_api_expr_v1alpha1_eval_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use EvalState.ProtoReflect.Descriptor instead.
func (*EvalState) Descriptor() ([]byte, []int) {
	return file_google_api_expr_v1alpha1_eval_proto_rawDescGZIP(), []int{0}
}

func (x *EvalState) GetValues() []*ExprValue {
	if x != nil {
		return x.Values
	}
	return nil
}

func (x *EvalState) GetResults() []*EvalState_Result {
	if x != nil {
		return x.Results
	}
	return nil
}

// The value of an evaluated expression.
type ExprValue struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// An expression can resolve to a value, error or unknown.
	//
	// Types that are assignable to Kind:
	//	*ExprValue_Value
	//	*ExprValue_Error
	//	*ExprValue_Unknown
	Kind isExprValue_Kind `protobuf_oneof:"kind"`
}

func (x *ExprValue) Reset() {
	*x = ExprValue{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_api_expr_v1alpha1_eval_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ExprValue) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ExprValue) ProtoMessage() {}

func (x *ExprValue) ProtoReflect() protoreflect.Message {
	mi := &file_google_api_expr_v1alpha1_eval_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ExprValue.ProtoReflect.Descriptor instead.
func (*ExprValue) Descriptor() ([]byte, []int) {
	return file_google_api_expr_v1alpha1_eval_proto_rawDescGZIP(), []int{1}
}

func (m *ExprValue) GetKind() isExprValue_Kind {
	if m != nil {
		return m.Kind
	}
	return nil
}

func (x *ExprValue) GetValue() *Value {
	if x, ok := x.GetKind().(*ExprValue_Value); ok {
		return x.Value
	}
	return nil
}

func (x *ExprValue) GetError() *ErrorSet {
	if x, ok := x.GetKind().(*ExprValue_Error); ok {
		return x.Error
	}
	return nil
}

func (x *ExprValue) GetUnknown() *UnknownSet {
	if x, ok := x.GetKind().(*ExprValue_Unknown); ok {
		return x.Unknown
	}
	return nil
}

type isExprValue_Kind interface {
	isExprValue_Kind()
}

type ExprValue_Value struct {
	// A concrete value.
	Value *Value `protobuf:"bytes,1,opt,name=value,proto3,oneof"`
}

type ExprValue_Error struct {
	// The set of errors in the critical path of evalution.
	//
	// Only errors in the critical path are included. For example,
	// `(<error1> || true) && <error2>` will only result in `<error2>`,
	// while `<error1> || <error2>` will result in both `<error1>` and
	// `<error2>`.
	//
	// Errors cause by the presence of other errors are not included in the
	// set. For example `<error1>.foo`, `foo(<error1>)`, and `<error1> + 1` will
	// only result in `<error1>`.
	//
	// Multiple errors *might* be included when evaluation could result
	// in different errors. For example `<error1> + <error2>` and
	// `foo(<error1>, <error2>)` may result in `<error1>`, `<error2>` or both.
	// The exact subset of errors included for this case is unspecified and
	// depends on the implementation details of the evaluator.
	Error *ErrorSet `protobuf:"bytes,2,opt,name=error,proto3,oneof"`
}

type ExprValue_Unknown struct {
	// The set of unknowns in the critical path of evaluation.
	//
	// Unknown behaves identically to Error with regards to propagation.
	// Specifically, only unknowns in the critical path are included, unknowns
	// caused by the presence of other unknowns are not included, and multiple
	// unknowns *might* be included included when evaluation could result in
	// different unknowns. For example:
	//
	//     (<unknown[1]> || true) && <unknown[2]> -> <unknown[2]>
	//     <unknown[1]> || <unknown[2]> -> <unknown[1,2]>
	//     <unknown[1]>.foo -> <unknown[1]>
	//     foo(<unknown[1]>) -> <unknown[1]>
	//     <unknown[1]> + <unknown[2]> -> <unknown[1]> or <unknown[2[>
	//
	// Unknown takes precidence over Error in cases where a `Value` can short
	// circuit the result:
	//
	//     <error> || <unknown> -> <unknown>
	//     <error> && <unknown> -> <unknown>
	//
	// Errors take precidence in all other cases:
	//
	//     <unknown> + <error> -> <error>
	//     foo(<unknown>, <error>) -> <error>
	Unknown *UnknownSet `protobuf:"bytes,3,opt,name=unknown,proto3,oneof"`
}

func (*ExprValue_Value) isExprValue_Kind() {}

func (*ExprValue_Error) isExprValue_Kind() {}

func (*ExprValue_Unknown) isExprValue_Kind() {}

// A set of errors.
//
// The errors included depend on the context. See `ExprValue.error`.
type ErrorSet struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// The errors in the set.
	Errors []*status.Status `protobuf:"bytes,1,rep,name=errors,proto3" json:"errors,omitempty"`
}

func (x *ErrorSet) Reset() {
	*x = ErrorSet{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_api_expr_v1alpha1_eval_proto_msgTypes[2]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ErrorSet) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ErrorSet) ProtoMessage() {}

func (x *ErrorSet) ProtoReflect() protoreflect.Message {
	mi := &file_google_api_expr_v1alpha1_eval_proto_msgTypes[2]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ErrorSet.ProtoReflect.Descriptor instead.
func (*ErrorSet) Descriptor() ([]byte, []int) {
	return file_google_api_expr_v1alpha1_eval_proto_rawDescGZIP(), []int{2}
}

func (x *ErrorSet) GetErrors() []*status.Status {
	if x != nil {
		return x.Errors
	}
	return nil
}

// A set of expressions for which the value is unknown.
//
// The unknowns included depend on the context. See `ExprValue.unknown`.
type UnknownSet struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// The ids of the expressions with unknown values.
	Exprs []int64 `protobuf:"varint,1,rep,packed,name=exprs,proto3" json:"exprs,omitempty"`
}

func (x *UnknownSet) Reset() {
	*x = UnknownSet{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_api_expr_v1alpha1_eval_proto_msgTypes[3]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *UnknownSet) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*UnknownSet) ProtoMessage() {}

func (x *UnknownSet) ProtoReflect() protoreflect.Message {
	mi := &file_google_api_expr_v1alpha1_eval_proto_msgTypes[3]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use UnknownSet.ProtoReflect.Descriptor instead.
func (*UnknownSet) Descriptor() ([]byte, []int) {
	return file_google_api_expr_v1alpha1_eval_proto_rawDescGZIP(), []int{3}
}

func (x *UnknownSet) GetExprs() []int64 {
	if x != nil {
		return x.Exprs
	}
	return nil
}

// A single evalution result.
type EvalState_Result struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// The id of the expression this result if for.
	Expr int64 `protobuf:"varint,1,opt,name=expr,proto3" json:"expr,omitempty"`
	// The index in `values` of the resulting value.
	Value int64 `protobuf:"varint,2,opt,name=value,proto3" json:"value,omitempty"`
}

func (x *EvalState_Result) Reset() {
	*x = EvalState_Result{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_api_expr_v1alpha1_eval_proto_msgTypes[4]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *EvalState_Result) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*EvalState_Result) ProtoMessage() {}

func (x *EvalState_Result) ProtoReflect() protoreflect.Message {
	mi := &file_google_api_expr_v1alpha1_eval_proto_msgTypes[4]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use EvalState_Result.ProtoReflect.Descriptor instead.
func (*EvalState_Result) Descriptor() ([]byte, []int) {
	return file_google_api_expr_v1alpha1_eval_proto_rawDescGZIP(), []int{0, 0}
}

func (x *EvalState_Result) GetExpr() int64 {
	if x != nil {
		return x.Expr
	}
	return 0
}

func (x *EvalState_Result) GetValue() int64 {
	if x != nil {
		return x.Value
	}
	return 0
}

var File_google_api_expr_v1alpha1_eval_proto protoreflect.FileDescriptor

var file_google_api_expr_v1alpha1_eval_proto_rawDesc = []byte{
	0x0a, 0x23, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x65, 0x78, 0x70,
	0x72, 0x2f, 0x76, 0x31, 0x61, 0x6c, 0x70, 0x68, 0x61, 0x31, 0x2f, 0x65, 0x76, 0x61, 0x6c, 0x2e,
	0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x18, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70,
	0x69, 0x2e, 0x65, 0x78, 0x70, 0x72, 0x2e, 0x76, 0x31, 0x61, 0x6c, 0x70, 0x68, 0x61, 0x31, 0x1a,
	0x24, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x65, 0x78, 0x70, 0x72,
	0x2f, 0x76, 0x31, 0x61, 0x6c, 0x70, 0x68, 0x61, 0x31, 0x2f, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x2e,
	0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x17, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x72, 0x70,
	0x63, 0x2f, 0x73, 0x74, 0x61, 0x74, 0x75, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22, 0xc2,
	0x01, 0x0a, 0x09, 0x45, 0x76, 0x61, 0x6c, 0x53, 0x74, 0x61, 0x74, 0x65, 0x12, 0x3b, 0x0a, 0x06,
	0x76, 0x61, 0x6c, 0x75, 0x65, 0x73, 0x18, 0x01, 0x20, 0x03, 0x28, 0x0b, 0x32, 0x23, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x65, 0x78, 0x70, 0x72, 0x2e, 0x76,
	0x31, 0x61, 0x6c, 0x70, 0x68, 0x61, 0x31, 0x2e, 0x45, 0x78, 0x70, 0x72, 0x56, 0x61, 0x6c, 0x75,
	0x65, 0x52, 0x06, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x73, 0x12, 0x44, 0x0a, 0x07, 0x72, 0x65, 0x73,
	0x75, 0x6c, 0x74, 0x73, 0x18, 0x03, 0x20, 0x03, 0x28, 0x0b, 0x32, 0x2a, 0x2e, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x65, 0x78, 0x70, 0x72, 0x2e, 0x76, 0x31, 0x61,
	0x6c, 0x70, 0x68, 0x61, 0x31, 0x2e, 0x45, 0x76, 0x61, 0x6c, 0x53, 0x74, 0x61, 0x74, 0x65, 0x2e,
	0x52, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x52, 0x07, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73, 0x1a,
	0x32, 0x0a, 0x06, 0x52, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x12, 0x12, 0x0a, 0x04, 0x65, 0x78, 0x70,
	0x72, 0x18, 0x01, 0x20, 0x01, 0x28, 0x03, 0x52, 0x04, 0x65, 0x78, 0x70, 0x72, 0x12, 0x14, 0x0a,
	0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x18, 0x02, 0x20, 0x01, 0x28, 0x03, 0x52, 0x05, 0x76, 0x61,
	0x6c, 0x75, 0x65, 0x22, 0xca, 0x01, 0x0a, 0x09, 0x45, 0x78, 0x70, 0x72, 0x56, 0x61, 0x6c, 0x75,
	0x65, 0x12, 0x37, 0x0a, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28, 0x0b,
	0x32, 0x1f, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x65, 0x78,
	0x70, 0x72, 0x2e, 0x76, 0x31, 0x61, 0x6c, 0x70, 0x68, 0x61, 0x31, 0x2e, 0x56, 0x61, 0x6c, 0x75,
	0x65, 0x48, 0x00, 0x52, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x12, 0x3a, 0x0a, 0x05, 0x65, 0x72,
	0x72, 0x6f, 0x72, 0x18, 0x02, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x22, 0x2e, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x65, 0x78, 0x70, 0x72, 0x2e, 0x76, 0x31, 0x61, 0x6c,
	0x70, 0x68, 0x61, 0x31, 0x2e, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x53, 0x65, 0x74, 0x48, 0x00, 0x52,
	0x05, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x12, 0x40, 0x0a, 0x07, 0x75, 0x6e, 0x6b, 0x6e, 0x6f, 0x77,
	0x6e, 0x18, 0x03, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x24, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x2e, 0x61, 0x70, 0x69, 0x2e, 0x65, 0x78, 0x70, 0x72, 0x2e, 0x76, 0x31, 0x61, 0x6c, 0x70, 0x68,
	0x61, 0x31, 0x2e, 0x55, 0x6e, 0x6b, 0x6e, 0x6f, 0x77, 0x6e, 0x53, 0x65, 0x74, 0x48, 0x00, 0x52,
	0x07, 0x75, 0x6e, 0x6b, 0x6e, 0x6f, 0x77, 0x6e, 0x42, 0x06, 0x0a, 0x04, 0x6b, 0x69, 0x6e, 0x64,
	0x22, 0x36, 0x0a, 0x08, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x53, 0x65, 0x74, 0x12, 0x2a, 0x0a, 0x06,
	0x65, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x18, 0x01, 0x20, 0x03, 0x28, 0x0b, 0x32, 0x12, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x72, 0x70, 0x63, 0x2e, 0x53, 0x74, 0x61, 0x74, 0x75, 0x73,
	0x52, 0x06, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x22, 0x22, 0x0a, 0x0a, 0x55, 0x6e, 0x6b, 0x6e,
	0x6f, 0x77, 0x6e, 0x53, 0x65, 0x74, 0x12, 0x14, 0x0a, 0x05, 0x65, 0x78, 0x70, 0x72, 0x73, 0x18,
	0x01, 0x20, 0x03, 0x28, 0x03, 0x52, 0x05, 0x65, 0x78, 0x70, 0x72, 0x73, 0x42, 0x6c, 0x0a, 0x1c,
	0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x65,
	0x78, 0x70, 0x72, 0x2e, 0x76, 0x31, 0x61, 0x6c, 0x70, 0x68, 0x61, 0x31, 0x42, 0x09, 0x45, 0x76,
	0x61, 0x6c, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a, 0x3c, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e,
	0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73,
	0x2f, 0x61, 0x70, 0x69, 0x2f, 0x65, 0x78, 0x70, 0x72, 0x2f, 0x76, 0x31, 0x61, 0x6c, 0x70, 0x68,
	0x61, 0x31, 0x3b, 0x65, 0x78, 0x70, 0x72, 0xf8, 0x01, 0x01, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74,
	0x6f, 0x33,
}

var (
	file_google_api_expr_v1alpha1_eval_proto_rawDescOnce sync.Once
	file_google_api_expr_v1alpha1_eval_proto_rawDescData = file_google_api_expr_v1alpha1_eval_proto_rawDesc
)

func file_google_api_expr_v1alpha1_eval_proto_rawDescGZIP() []byte {
	file_google_api_expr_v1alpha1_eval_proto_rawDescOnce.Do(func() {
		file_google_api_expr_v1alpha1_eval_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_api_expr_v1alpha1_eval_proto_rawDescData)
	})
	return file_google_api_expr_v1alpha1_eval_proto_rawDescData
}

var file_google_api_expr_v1alpha1_eval_proto_msgTypes = make([]protoimpl.MessageInfo, 5)
var file_google_api_expr_v1alpha1_eval_proto_goTypes = []interface{}{
	(*EvalState)(nil),        // 0: google.api.expr.v1alpha1.EvalState
	(*ExprValue)(nil),        // 1: google.api.expr.v1alpha1.ExprValue
	(*ErrorSet)(nil),         // 2: google.api.expr.v1alpha1.ErrorSet
	(*UnknownSet)(nil),       // 3: google.api.expr.v1alpha1.UnknownSet
	(*EvalState_Result)(nil), // 4: google.api.expr.v1alpha1.EvalState.Result
	(*Value)(nil),            // 5: google.api.expr.v1alpha1.Value
	(*status.Status)(nil),    // 6: google.rpc.Status
}
var file_google_api_expr_v1alpha1_eval_proto_depIdxs = []int32{
	1, // 0: google.api.expr.v1alpha1.EvalState.values:type_name -> google.api.expr.v1alpha1.ExprValue
	4, // 1: google.api.expr.v1alpha1.EvalState.results:type_name -> google.api.expr.v1alpha1.EvalState.Result
	5, // 2: google.api.expr.v1alpha1.ExprValue.value:type_name -> google.api.expr.v1alpha1.Value
	2, // 3: google.api.expr.v1alpha1.ExprValue.error:type_name -> google.api.expr.v1alpha1.ErrorSet
	3, // 4: google.api.expr.v1alpha1.ExprValue.unknown:type_name -> google.api.expr.v1alpha1.UnknownSet
	6, // 5: google.api.expr.v1alpha1.ErrorSet.errors:type_name -> google.rpc.Status
	6, // [6:6] is the sub-list for method output_type
	6, // [6:6] is the sub-list for method input_type
	6, // [6:6] is the sub-list for extension type_name
	6, // [6:6] is the sub-list for extension extendee
	0, // [0:6] is the sub-list for field type_name
}

func init() { file_google_api_expr_v1alpha1_eval_proto_init() }
func file_google_api_expr_v1alpha1_eval_proto_init() {
	if File_google_api_expr_v1alpha1_eval_proto != nil {
		return
	}
	file_google_api_expr_v1alpha1_value_proto_init()
	if !protoimpl.UnsafeEnabled {
		file_google_api_expr_v1alpha1_eval_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*EvalState); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_google_api_expr_v1alpha1_eval_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ExprValue); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_google_api_expr_v1alpha1_eval_proto_msgTypes[2].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ErrorSet); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_google_api_expr_v1alpha1_eval_proto_msgTypes[3].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*UnknownSet); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_google_api_expr_v1alpha1_eval_proto_msgTypes[4].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*EvalState_Result); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
	}
	file_google_api_expr_v1alpha1_eval_proto_msgTypes[1].OneofWrappers = []interface{}{
		(*ExprValue_Value)(nil),
		(*ExprValue_Error)(nil),
		(*ExprValue_Unknown)(nil),
	}
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: file_google_api_expr_v1alpha1_eval_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   5,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_api_expr_v1alpha1_eval_proto_goTypes,
		DependencyIndexes: file_google_api_expr_v1alpha1_eval_proto_depIdxs,
		MessageInfos:      file_google_api_expr_v1alpha1_eval_proto_msgTypes,
	}.Build()
	File_google_api_expr_v1alpha1_eval_proto = out.File
	file_google_api_expr_v1alpha1_eval_proto_rawDesc = nil
	file_google_api_expr_v1alpha1_eval_proto_goTypes = nil
	file_google_api_expr_v1alpha1_eval_proto_depIdxs = nil
}
