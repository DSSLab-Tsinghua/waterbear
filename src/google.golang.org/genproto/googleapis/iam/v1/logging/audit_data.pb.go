// Copyright 2017 Google Inc.
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
// source: google/iam/v1/logging/audit_data.proto

package logging

import (
	reflect "reflect"
	sync "sync"

	proto "github.com/golang/protobuf/proto"
	_ "google.golang.org/genproto/googleapis/api/annotations"
	v1 "google.golang.org/genproto/googleapis/iam/v1"
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

// Audit log information specific to Cloud IAM. This message is serialized
// as an `Any` type in the `ServiceData` message of an
// `AuditLog` message.
type AuditData struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Policy delta between the original policy and the newly set policy.
	PolicyDelta *v1.PolicyDelta `protobuf:"bytes,2,opt,name=policy_delta,json=policyDelta,proto3" json:"policy_delta,omitempty"`
}

func (x *AuditData) Reset() {
	*x = AuditData{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_iam_v1_logging_audit_data_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *AuditData) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*AuditData) ProtoMessage() {}

func (x *AuditData) ProtoReflect() protoreflect.Message {
	mi := &file_google_iam_v1_logging_audit_data_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use AuditData.ProtoReflect.Descriptor instead.
func (*AuditData) Descriptor() ([]byte, []int) {
	return file_google_iam_v1_logging_audit_data_proto_rawDescGZIP(), []int{0}
}

func (x *AuditData) GetPolicyDelta() *v1.PolicyDelta {
	if x != nil {
		return x.PolicyDelta
	}
	return nil
}

var File_google_iam_v1_logging_audit_data_proto protoreflect.FileDescriptor

var file_google_iam_v1_logging_audit_data_proto_rawDesc = []byte{
	0x0a, 0x26, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x69, 0x61, 0x6d, 0x2f, 0x76, 0x31, 0x2f,
	0x6c, 0x6f, 0x67, 0x67, 0x69, 0x6e, 0x67, 0x2f, 0x61, 0x75, 0x64, 0x69, 0x74, 0x5f, 0x64, 0x61,
	0x74, 0x61, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x15, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x2e, 0x69, 0x61, 0x6d, 0x2e, 0x76, 0x31, 0x2e, 0x6c, 0x6f, 0x67, 0x67, 0x69, 0x6e, 0x67, 0x1a,
	0x1c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x61, 0x6e, 0x6e, 0x6f,
	0x74, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x1a, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x69, 0x61, 0x6d, 0x2f, 0x76, 0x31, 0x2f, 0x70, 0x6f, 0x6c,
	0x69, 0x63, 0x79, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22, 0x4a, 0x0a, 0x09, 0x41, 0x75, 0x64,
	0x69, 0x74, 0x44, 0x61, 0x74, 0x61, 0x12, 0x3d, 0x0a, 0x0c, 0x70, 0x6f, 0x6c, 0x69, 0x63, 0x79,
	0x5f, 0x64, 0x65, 0x6c, 0x74, 0x61, 0x18, 0x02, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x1a, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x69, 0x61, 0x6d, 0x2e, 0x76, 0x31, 0x2e, 0x50, 0x6f, 0x6c,
	0x69, 0x63, 0x79, 0x44, 0x65, 0x6c, 0x74, 0x61, 0x52, 0x0b, 0x70, 0x6f, 0x6c, 0x69, 0x63, 0x79,
	0x44, 0x65, 0x6c, 0x74, 0x61, 0x42, 0x89, 0x01, 0x0a, 0x19, 0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x69, 0x61, 0x6d, 0x2e, 0x76, 0x31, 0x2e, 0x6c, 0x6f, 0x67, 0x67,
	0x69, 0x6e, 0x67, 0x42, 0x0e, 0x41, 0x75, 0x64, 0x69, 0x74, 0x44, 0x61, 0x74, 0x61, 0x50, 0x72,
	0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a, 0x3c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f,
	0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74,
	0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x69, 0x61, 0x6d,
	0x2f, 0x76, 0x31, 0x2f, 0x6c, 0x6f, 0x67, 0x67, 0x69, 0x6e, 0x67, 0x3b, 0x6c, 0x6f, 0x67, 0x67,
	0x69, 0x6e, 0x67, 0xaa, 0x02, 0x1b, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x43, 0x6c, 0x6f,
	0x75, 0x64, 0x2e, 0x49, 0x61, 0x6d, 0x2e, 0x56, 0x31, 0x2e, 0x4c, 0x6f, 0x67, 0x67, 0x69, 0x6e,
	0x67, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_iam_v1_logging_audit_data_proto_rawDescOnce sync.Once
	file_google_iam_v1_logging_audit_data_proto_rawDescData = file_google_iam_v1_logging_audit_data_proto_rawDesc
)

func file_google_iam_v1_logging_audit_data_proto_rawDescGZIP() []byte {
	file_google_iam_v1_logging_audit_data_proto_rawDescOnce.Do(func() {
		file_google_iam_v1_logging_audit_data_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_iam_v1_logging_audit_data_proto_rawDescData)
	})
	return file_google_iam_v1_logging_audit_data_proto_rawDescData
}

var file_google_iam_v1_logging_audit_data_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_iam_v1_logging_audit_data_proto_goTypes = []interface{}{
	(*AuditData)(nil),      // 0: google.iam.v1.logging.AuditData
	(*v1.PolicyDelta)(nil), // 1: google.iam.v1.PolicyDelta
}
var file_google_iam_v1_logging_audit_data_proto_depIdxs = []int32{
	1, // 0: google.iam.v1.logging.AuditData.policy_delta:type_name -> google.iam.v1.PolicyDelta
	1, // [1:1] is the sub-list for method output_type
	1, // [1:1] is the sub-list for method input_type
	1, // [1:1] is the sub-list for extension type_name
	1, // [1:1] is the sub-list for extension extendee
	0, // [0:1] is the sub-list for field type_name
}

func init() { file_google_iam_v1_logging_audit_data_proto_init() }
func file_google_iam_v1_logging_audit_data_proto_init() {
	if File_google_iam_v1_logging_audit_data_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_iam_v1_logging_audit_data_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*AuditData); i {
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
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: file_google_iam_v1_logging_audit_data_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_iam_v1_logging_audit_data_proto_goTypes,
		DependencyIndexes: file_google_iam_v1_logging_audit_data_proto_depIdxs,
		MessageInfos:      file_google_iam_v1_logging_audit_data_proto_msgTypes,
	}.Build()
	File_google_iam_v1_logging_audit_data_proto = out.File
	file_google_iam_v1_logging_audit_data_proto_rawDesc = nil
	file_google_iam_v1_logging_audit_data_proto_goTypes = nil
	file_google_iam_v1_logging_audit_data_proto_depIdxs = nil
}
