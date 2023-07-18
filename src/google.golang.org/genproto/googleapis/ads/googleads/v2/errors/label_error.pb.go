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
// source: google/ads/googleads/v2/errors/label_error.proto

package errors

import (
	reflect "reflect"
	sync "sync"

	proto "github.com/golang/protobuf/proto"
	_ "google.golang.org/genproto/googleapis/api/annotations"
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

// Enum describing possible label errors.
type LabelErrorEnum_LabelError int32

const (
	// Enum unspecified.
	LabelErrorEnum_UNSPECIFIED LabelErrorEnum_LabelError = 0
	// The received error code is not known in this version.
	LabelErrorEnum_UNKNOWN LabelErrorEnum_LabelError = 1
	// An inactive label cannot be applied.
	LabelErrorEnum_CANNOT_APPLY_INACTIVE_LABEL LabelErrorEnum_LabelError = 2
	// A label cannot be applied to a disabled ad group criterion.
	LabelErrorEnum_CANNOT_APPLY_LABEL_TO_DISABLED_AD_GROUP_CRITERION LabelErrorEnum_LabelError = 3
	// A label cannot be applied to a negative ad group criterion.
	LabelErrorEnum_CANNOT_APPLY_LABEL_TO_NEGATIVE_AD_GROUP_CRITERION LabelErrorEnum_LabelError = 4
	// Cannot apply more than 50 labels per resource.
	LabelErrorEnum_EXCEEDED_LABEL_LIMIT_PER_TYPE LabelErrorEnum_LabelError = 5
	// Labels from a manager account cannot be applied to campaign, ad group,
	// ad group ad, or ad group criterion resources.
	LabelErrorEnum_INVALID_RESOURCE_FOR_MANAGER_LABEL LabelErrorEnum_LabelError = 6
	// Label names must be unique.
	LabelErrorEnum_DUPLICATE_NAME LabelErrorEnum_LabelError = 7
	// Label names cannot be empty.
	LabelErrorEnum_INVALID_LABEL_NAME LabelErrorEnum_LabelError = 8
	// Labels cannot be applied to a draft.
	LabelErrorEnum_CANNOT_ATTACH_LABEL_TO_DRAFT LabelErrorEnum_LabelError = 9
	// Labels not from a manager account cannot be applied to the customer
	// resource.
	LabelErrorEnum_CANNOT_ATTACH_NON_MANAGER_LABEL_TO_CUSTOMER LabelErrorEnum_LabelError = 10
)

// Enum value maps for LabelErrorEnum_LabelError.
var (
	LabelErrorEnum_LabelError_name = map[int32]string{
		0:  "UNSPECIFIED",
		1:  "UNKNOWN",
		2:  "CANNOT_APPLY_INACTIVE_LABEL",
		3:  "CANNOT_APPLY_LABEL_TO_DISABLED_AD_GROUP_CRITERION",
		4:  "CANNOT_APPLY_LABEL_TO_NEGATIVE_AD_GROUP_CRITERION",
		5:  "EXCEEDED_LABEL_LIMIT_PER_TYPE",
		6:  "INVALID_RESOURCE_FOR_MANAGER_LABEL",
		7:  "DUPLICATE_NAME",
		8:  "INVALID_LABEL_NAME",
		9:  "CANNOT_ATTACH_LABEL_TO_DRAFT",
		10: "CANNOT_ATTACH_NON_MANAGER_LABEL_TO_CUSTOMER",
	}
	LabelErrorEnum_LabelError_value = map[string]int32{
		"UNSPECIFIED":                 0,
		"UNKNOWN":                     1,
		"CANNOT_APPLY_INACTIVE_LABEL": 2,
		"CANNOT_APPLY_LABEL_TO_DISABLED_AD_GROUP_CRITERION": 3,
		"CANNOT_APPLY_LABEL_TO_NEGATIVE_AD_GROUP_CRITERION": 4,
		"EXCEEDED_LABEL_LIMIT_PER_TYPE":                     5,
		"INVALID_RESOURCE_FOR_MANAGER_LABEL":                6,
		"DUPLICATE_NAME":                                    7,
		"INVALID_LABEL_NAME":                                8,
		"CANNOT_ATTACH_LABEL_TO_DRAFT":                      9,
		"CANNOT_ATTACH_NON_MANAGER_LABEL_TO_CUSTOMER":       10,
	}
)

func (x LabelErrorEnum_LabelError) Enum() *LabelErrorEnum_LabelError {
	p := new(LabelErrorEnum_LabelError)
	*p = x
	return p
}

func (x LabelErrorEnum_LabelError) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (LabelErrorEnum_LabelError) Descriptor() protoreflect.EnumDescriptor {
	return file_google_ads_googleads_v2_errors_label_error_proto_enumTypes[0].Descriptor()
}

func (LabelErrorEnum_LabelError) Type() protoreflect.EnumType {
	return &file_google_ads_googleads_v2_errors_label_error_proto_enumTypes[0]
}

func (x LabelErrorEnum_LabelError) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use LabelErrorEnum_LabelError.Descriptor instead.
func (LabelErrorEnum_LabelError) EnumDescriptor() ([]byte, []int) {
	return file_google_ads_googleads_v2_errors_label_error_proto_rawDescGZIP(), []int{0, 0}
}

// Container for enum describing possible label errors.
type LabelErrorEnum struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *LabelErrorEnum) Reset() {
	*x = LabelErrorEnum{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v2_errors_label_error_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *LabelErrorEnum) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*LabelErrorEnum) ProtoMessage() {}

func (x *LabelErrorEnum) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v2_errors_label_error_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use LabelErrorEnum.ProtoReflect.Descriptor instead.
func (*LabelErrorEnum) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v2_errors_label_error_proto_rawDescGZIP(), []int{0}
}

var File_google_ads_googleads_v2_errors_label_error_proto protoreflect.FileDescriptor

var file_google_ads_googleads_v2_errors_label_error_proto_rawDesc = []byte{
	0x0a, 0x30, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x32, 0x2f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73,
	0x2f, 0x6c, 0x61, 0x62, 0x65, 0x6c, 0x5f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x2e, 0x70, 0x72, 0x6f,
	0x74, 0x6f, 0x12, 0x1e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x32, 0x2e, 0x65, 0x72, 0x72, 0x6f,
	0x72, 0x73, 0x1a, 0x1c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x61,
	0x6e, 0x6e, 0x6f, 0x74, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f,
	0x22, 0x96, 0x03, 0x0a, 0x0e, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x45,
	0x6e, 0x75, 0x6d, 0x22, 0x83, 0x03, 0x0a, 0x0a, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x45, 0x72, 0x72,
	0x6f, 0x72, 0x12, 0x0f, 0x0a, 0x0b, 0x55, 0x4e, 0x53, 0x50, 0x45, 0x43, 0x49, 0x46, 0x49, 0x45,
	0x44, 0x10, 0x00, 0x12, 0x0b, 0x0a, 0x07, 0x55, 0x4e, 0x4b, 0x4e, 0x4f, 0x57, 0x4e, 0x10, 0x01,
	0x12, 0x1f, 0x0a, 0x1b, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x41, 0x50, 0x50, 0x4c, 0x59,
	0x5f, 0x49, 0x4e, 0x41, 0x43, 0x54, 0x49, 0x56, 0x45, 0x5f, 0x4c, 0x41, 0x42, 0x45, 0x4c, 0x10,
	0x02, 0x12, 0x35, 0x0a, 0x31, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x41, 0x50, 0x50, 0x4c,
	0x59, 0x5f, 0x4c, 0x41, 0x42, 0x45, 0x4c, 0x5f, 0x54, 0x4f, 0x5f, 0x44, 0x49, 0x53, 0x41, 0x42,
	0x4c, 0x45, 0x44, 0x5f, 0x41, 0x44, 0x5f, 0x47, 0x52, 0x4f, 0x55, 0x50, 0x5f, 0x43, 0x52, 0x49,
	0x54, 0x45, 0x52, 0x49, 0x4f, 0x4e, 0x10, 0x03, 0x12, 0x35, 0x0a, 0x31, 0x43, 0x41, 0x4e, 0x4e,
	0x4f, 0x54, 0x5f, 0x41, 0x50, 0x50, 0x4c, 0x59, 0x5f, 0x4c, 0x41, 0x42, 0x45, 0x4c, 0x5f, 0x54,
	0x4f, 0x5f, 0x4e, 0x45, 0x47, 0x41, 0x54, 0x49, 0x56, 0x45, 0x5f, 0x41, 0x44, 0x5f, 0x47, 0x52,
	0x4f, 0x55, 0x50, 0x5f, 0x43, 0x52, 0x49, 0x54, 0x45, 0x52, 0x49, 0x4f, 0x4e, 0x10, 0x04, 0x12,
	0x21, 0x0a, 0x1d, 0x45, 0x58, 0x43, 0x45, 0x45, 0x44, 0x45, 0x44, 0x5f, 0x4c, 0x41, 0x42, 0x45,
	0x4c, 0x5f, 0x4c, 0x49, 0x4d, 0x49, 0x54, 0x5f, 0x50, 0x45, 0x52, 0x5f, 0x54, 0x59, 0x50, 0x45,
	0x10, 0x05, 0x12, 0x26, 0x0a, 0x22, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x52, 0x45,
	0x53, 0x4f, 0x55, 0x52, 0x43, 0x45, 0x5f, 0x46, 0x4f, 0x52, 0x5f, 0x4d, 0x41, 0x4e, 0x41, 0x47,
	0x45, 0x52, 0x5f, 0x4c, 0x41, 0x42, 0x45, 0x4c, 0x10, 0x06, 0x12, 0x12, 0x0a, 0x0e, 0x44, 0x55,
	0x50, 0x4c, 0x49, 0x43, 0x41, 0x54, 0x45, 0x5f, 0x4e, 0x41, 0x4d, 0x45, 0x10, 0x07, 0x12, 0x16,
	0x0a, 0x12, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x4c, 0x41, 0x42, 0x45, 0x4c, 0x5f,
	0x4e, 0x41, 0x4d, 0x45, 0x10, 0x08, 0x12, 0x20, 0x0a, 0x1c, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54,
	0x5f, 0x41, 0x54, 0x54, 0x41, 0x43, 0x48, 0x5f, 0x4c, 0x41, 0x42, 0x45, 0x4c, 0x5f, 0x54, 0x4f,
	0x5f, 0x44, 0x52, 0x41, 0x46, 0x54, 0x10, 0x09, 0x12, 0x2f, 0x0a, 0x2b, 0x43, 0x41, 0x4e, 0x4e,
	0x4f, 0x54, 0x5f, 0x41, 0x54, 0x54, 0x41, 0x43, 0x48, 0x5f, 0x4e, 0x4f, 0x4e, 0x5f, 0x4d, 0x41,
	0x4e, 0x41, 0x47, 0x45, 0x52, 0x5f, 0x4c, 0x41, 0x42, 0x45, 0x4c, 0x5f, 0x54, 0x4f, 0x5f, 0x43,
	0x55, 0x53, 0x54, 0x4f, 0x4d, 0x45, 0x52, 0x10, 0x0a, 0x42, 0xea, 0x01, 0x0a, 0x22, 0x63, 0x6f,
	0x6d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x32, 0x2e, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73,
	0x42, 0x0f, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x50, 0x72, 0x6f, 0x74,
	0x6f, 0x50, 0x01, 0x5a, 0x44, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61,
	0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x32, 0x2f, 0x65, 0x72, 0x72, 0x6f,
	0x72, 0x73, 0x3b, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73, 0xa2, 0x02, 0x03, 0x47, 0x41, 0x41, 0xaa,
	0x02, 0x1e, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x41, 0x64, 0x73, 0x2e, 0x47, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x2e, 0x56, 0x32, 0x2e, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x73,
	0xca, 0x02, 0x1e, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x5c, 0x41, 0x64, 0x73, 0x5c, 0x47, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x5c, 0x56, 0x32, 0x5c, 0x45, 0x72, 0x72, 0x6f, 0x72,
	0x73, 0xea, 0x02, 0x22, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x3a, 0x3a, 0x41, 0x64, 0x73, 0x3a,
	0x3a, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x3a, 0x3a, 0x56, 0x32, 0x3a, 0x3a,
	0x45, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_ads_googleads_v2_errors_label_error_proto_rawDescOnce sync.Once
	file_google_ads_googleads_v2_errors_label_error_proto_rawDescData = file_google_ads_googleads_v2_errors_label_error_proto_rawDesc
)

func file_google_ads_googleads_v2_errors_label_error_proto_rawDescGZIP() []byte {
	file_google_ads_googleads_v2_errors_label_error_proto_rawDescOnce.Do(func() {
		file_google_ads_googleads_v2_errors_label_error_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_ads_googleads_v2_errors_label_error_proto_rawDescData)
	})
	return file_google_ads_googleads_v2_errors_label_error_proto_rawDescData
}

var file_google_ads_googleads_v2_errors_label_error_proto_enumTypes = make([]protoimpl.EnumInfo, 1)
var file_google_ads_googleads_v2_errors_label_error_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_ads_googleads_v2_errors_label_error_proto_goTypes = []interface{}{
	(LabelErrorEnum_LabelError)(0), // 0: google.ads.googleads.v2.errors.LabelErrorEnum.LabelError
	(*LabelErrorEnum)(nil),         // 1: google.ads.googleads.v2.errors.LabelErrorEnum
}
var file_google_ads_googleads_v2_errors_label_error_proto_depIdxs = []int32{
	0, // [0:0] is the sub-list for method output_type
	0, // [0:0] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() { file_google_ads_googleads_v2_errors_label_error_proto_init() }
func file_google_ads_googleads_v2_errors_label_error_proto_init() {
	if File_google_ads_googleads_v2_errors_label_error_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_ads_googleads_v2_errors_label_error_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*LabelErrorEnum); i {
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
			RawDescriptor: file_google_ads_googleads_v2_errors_label_error_proto_rawDesc,
			NumEnums:      1,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_ads_googleads_v2_errors_label_error_proto_goTypes,
		DependencyIndexes: file_google_ads_googleads_v2_errors_label_error_proto_depIdxs,
		EnumInfos:         file_google_ads_googleads_v2_errors_label_error_proto_enumTypes,
		MessageInfos:      file_google_ads_googleads_v2_errors_label_error_proto_msgTypes,
	}.Build()
	File_google_ads_googleads_v2_errors_label_error_proto = out.File
	file_google_ads_googleads_v2_errors_label_error_proto_rawDesc = nil
	file_google_ads_googleads_v2_errors_label_error_proto_goTypes = nil
	file_google_ads_googleads_v2_errors_label_error_proto_depIdxs = nil
}
