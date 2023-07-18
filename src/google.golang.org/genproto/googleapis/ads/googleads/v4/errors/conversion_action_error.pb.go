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
// source: google/ads/googleads/v4/errors/conversion_action_error.proto

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

// Enum describing possible conversion action errors.
type ConversionActionErrorEnum_ConversionActionError int32

const (
	// Enum unspecified.
	ConversionActionErrorEnum_UNSPECIFIED ConversionActionErrorEnum_ConversionActionError = 0
	// The received error code is not known in this version.
	ConversionActionErrorEnum_UNKNOWN ConversionActionErrorEnum_ConversionActionError = 1
	// The specified conversion action name already exists.
	ConversionActionErrorEnum_DUPLICATE_NAME ConversionActionErrorEnum_ConversionActionError = 2
	// Another conversion action with the specified app id already exists.
	ConversionActionErrorEnum_DUPLICATE_APP_ID ConversionActionErrorEnum_ConversionActionError = 3
	// Android first open action conflicts with Google play codeless download
	// action tracking the same app.
	ConversionActionErrorEnum_TWO_CONVERSION_ACTIONS_BIDDING_ON_SAME_APP_DOWNLOAD ConversionActionErrorEnum_ConversionActionError = 4
	// Android first open action conflicts with Google play codeless download
	// action tracking the same app.
	ConversionActionErrorEnum_BIDDING_ON_SAME_APP_DOWNLOAD_AS_GLOBAL_ACTION ConversionActionErrorEnum_ConversionActionError = 5
	// The attribution model cannot be set to DATA_DRIVEN because a data-driven
	// model has never been generated.
	ConversionActionErrorEnum_DATA_DRIVEN_MODEL_WAS_NEVER_GENERATED ConversionActionErrorEnum_ConversionActionError = 6
	// The attribution model cannot be set to DATA_DRIVEN because the
	// data-driven model is expired.
	ConversionActionErrorEnum_DATA_DRIVEN_MODEL_EXPIRED ConversionActionErrorEnum_ConversionActionError = 7
	// The attribution model cannot be set to DATA_DRIVEN because the
	// data-driven model is stale.
	ConversionActionErrorEnum_DATA_DRIVEN_MODEL_STALE ConversionActionErrorEnum_ConversionActionError = 8
	// The attribution model cannot be set to DATA_DRIVEN because the
	// data-driven model is unavailable or the conversion action was newly
	// added.
	ConversionActionErrorEnum_DATA_DRIVEN_MODEL_UNKNOWN ConversionActionErrorEnum_ConversionActionError = 9
	// Creation of this conversion action type isn't supported by Google
	// Ads API.
	ConversionActionErrorEnum_CREATION_NOT_SUPPORTED ConversionActionErrorEnum_ConversionActionError = 10
)

// Enum value maps for ConversionActionErrorEnum_ConversionActionError.
var (
	ConversionActionErrorEnum_ConversionActionError_name = map[int32]string{
		0:  "UNSPECIFIED",
		1:  "UNKNOWN",
		2:  "DUPLICATE_NAME",
		3:  "DUPLICATE_APP_ID",
		4:  "TWO_CONVERSION_ACTIONS_BIDDING_ON_SAME_APP_DOWNLOAD",
		5:  "BIDDING_ON_SAME_APP_DOWNLOAD_AS_GLOBAL_ACTION",
		6:  "DATA_DRIVEN_MODEL_WAS_NEVER_GENERATED",
		7:  "DATA_DRIVEN_MODEL_EXPIRED",
		8:  "DATA_DRIVEN_MODEL_STALE",
		9:  "DATA_DRIVEN_MODEL_UNKNOWN",
		10: "CREATION_NOT_SUPPORTED",
	}
	ConversionActionErrorEnum_ConversionActionError_value = map[string]int32{
		"UNSPECIFIED":      0,
		"UNKNOWN":          1,
		"DUPLICATE_NAME":   2,
		"DUPLICATE_APP_ID": 3,
		"TWO_CONVERSION_ACTIONS_BIDDING_ON_SAME_APP_DOWNLOAD": 4,
		"BIDDING_ON_SAME_APP_DOWNLOAD_AS_GLOBAL_ACTION":       5,
		"DATA_DRIVEN_MODEL_WAS_NEVER_GENERATED":               6,
		"DATA_DRIVEN_MODEL_EXPIRED":                           7,
		"DATA_DRIVEN_MODEL_STALE":                             8,
		"DATA_DRIVEN_MODEL_UNKNOWN":                           9,
		"CREATION_NOT_SUPPORTED":                              10,
	}
)

func (x ConversionActionErrorEnum_ConversionActionError) Enum() *ConversionActionErrorEnum_ConversionActionError {
	p := new(ConversionActionErrorEnum_ConversionActionError)
	*p = x
	return p
}

func (x ConversionActionErrorEnum_ConversionActionError) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (ConversionActionErrorEnum_ConversionActionError) Descriptor() protoreflect.EnumDescriptor {
	return file_google_ads_googleads_v4_errors_conversion_action_error_proto_enumTypes[0].Descriptor()
}

func (ConversionActionErrorEnum_ConversionActionError) Type() protoreflect.EnumType {
	return &file_google_ads_googleads_v4_errors_conversion_action_error_proto_enumTypes[0]
}

func (x ConversionActionErrorEnum_ConversionActionError) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use ConversionActionErrorEnum_ConversionActionError.Descriptor instead.
func (ConversionActionErrorEnum_ConversionActionError) EnumDescriptor() ([]byte, []int) {
	return file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDescGZIP(), []int{0, 0}
}

// Container for enum describing possible conversion action errors.
type ConversionActionErrorEnum struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *ConversionActionErrorEnum) Reset() {
	*x = ConversionActionErrorEnum{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v4_errors_conversion_action_error_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ConversionActionErrorEnum) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ConversionActionErrorEnum) ProtoMessage() {}

func (x *ConversionActionErrorEnum) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v4_errors_conversion_action_error_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ConversionActionErrorEnum.ProtoReflect.Descriptor instead.
func (*ConversionActionErrorEnum) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDescGZIP(), []int{0}
}

var File_google_ads_googleads_v4_errors_conversion_action_error_proto protoreflect.FileDescriptor

var file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDesc = []byte{
	0x0a, 0x3c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x34, 0x2f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73,
	0x2f, 0x63, 0x6f, 0x6e, 0x76, 0x65, 0x72, 0x73, 0x69, 0x6f, 0x6e, 0x5f, 0x61, 0x63, 0x74, 0x69,
	0x6f, 0x6e, 0x5f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x1e,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x1a, 0x1c,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x61, 0x6e, 0x6e, 0x6f, 0x74,
	0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22, 0x8b, 0x03, 0x0a,
	0x19, 0x43, 0x6f, 0x6e, 0x76, 0x65, 0x72, 0x73, 0x69, 0x6f, 0x6e, 0x41, 0x63, 0x74, 0x69, 0x6f,
	0x6e, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x45, 0x6e, 0x75, 0x6d, 0x22, 0xed, 0x02, 0x0a, 0x15, 0x43,
	0x6f, 0x6e, 0x76, 0x65, 0x72, 0x73, 0x69, 0x6f, 0x6e, 0x41, 0x63, 0x74, 0x69, 0x6f, 0x6e, 0x45,
	0x72, 0x72, 0x6f, 0x72, 0x12, 0x0f, 0x0a, 0x0b, 0x55, 0x4e, 0x53, 0x50, 0x45, 0x43, 0x49, 0x46,
	0x49, 0x45, 0x44, 0x10, 0x00, 0x12, 0x0b, 0x0a, 0x07, 0x55, 0x4e, 0x4b, 0x4e, 0x4f, 0x57, 0x4e,
	0x10, 0x01, 0x12, 0x12, 0x0a, 0x0e, 0x44, 0x55, 0x50, 0x4c, 0x49, 0x43, 0x41, 0x54, 0x45, 0x5f,
	0x4e, 0x41, 0x4d, 0x45, 0x10, 0x02, 0x12, 0x14, 0x0a, 0x10, 0x44, 0x55, 0x50, 0x4c, 0x49, 0x43,
	0x41, 0x54, 0x45, 0x5f, 0x41, 0x50, 0x50, 0x5f, 0x49, 0x44, 0x10, 0x03, 0x12, 0x37, 0x0a, 0x33,
	0x54, 0x57, 0x4f, 0x5f, 0x43, 0x4f, 0x4e, 0x56, 0x45, 0x52, 0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x41,
	0x43, 0x54, 0x49, 0x4f, 0x4e, 0x53, 0x5f, 0x42, 0x49, 0x44, 0x44, 0x49, 0x4e, 0x47, 0x5f, 0x4f,
	0x4e, 0x5f, 0x53, 0x41, 0x4d, 0x45, 0x5f, 0x41, 0x50, 0x50, 0x5f, 0x44, 0x4f, 0x57, 0x4e, 0x4c,
	0x4f, 0x41, 0x44, 0x10, 0x04, 0x12, 0x31, 0x0a, 0x2d, 0x42, 0x49, 0x44, 0x44, 0x49, 0x4e, 0x47,
	0x5f, 0x4f, 0x4e, 0x5f, 0x53, 0x41, 0x4d, 0x45, 0x5f, 0x41, 0x50, 0x50, 0x5f, 0x44, 0x4f, 0x57,
	0x4e, 0x4c, 0x4f, 0x41, 0x44, 0x5f, 0x41, 0x53, 0x5f, 0x47, 0x4c, 0x4f, 0x42, 0x41, 0x4c, 0x5f,
	0x41, 0x43, 0x54, 0x49, 0x4f, 0x4e, 0x10, 0x05, 0x12, 0x29, 0x0a, 0x25, 0x44, 0x41, 0x54, 0x41,
	0x5f, 0x44, 0x52, 0x49, 0x56, 0x45, 0x4e, 0x5f, 0x4d, 0x4f, 0x44, 0x45, 0x4c, 0x5f, 0x57, 0x41,
	0x53, 0x5f, 0x4e, 0x45, 0x56, 0x45, 0x52, 0x5f, 0x47, 0x45, 0x4e, 0x45, 0x52, 0x41, 0x54, 0x45,
	0x44, 0x10, 0x06, 0x12, 0x1d, 0x0a, 0x19, 0x44, 0x41, 0x54, 0x41, 0x5f, 0x44, 0x52, 0x49, 0x56,
	0x45, 0x4e, 0x5f, 0x4d, 0x4f, 0x44, 0x45, 0x4c, 0x5f, 0x45, 0x58, 0x50, 0x49, 0x52, 0x45, 0x44,
	0x10, 0x07, 0x12, 0x1b, 0x0a, 0x17, 0x44, 0x41, 0x54, 0x41, 0x5f, 0x44, 0x52, 0x49, 0x56, 0x45,
	0x4e, 0x5f, 0x4d, 0x4f, 0x44, 0x45, 0x4c, 0x5f, 0x53, 0x54, 0x41, 0x4c, 0x45, 0x10, 0x08, 0x12,
	0x1d, 0x0a, 0x19, 0x44, 0x41, 0x54, 0x41, 0x5f, 0x44, 0x52, 0x49, 0x56, 0x45, 0x4e, 0x5f, 0x4d,
	0x4f, 0x44, 0x45, 0x4c, 0x5f, 0x55, 0x4e, 0x4b, 0x4e, 0x4f, 0x57, 0x4e, 0x10, 0x09, 0x12, 0x1a,
	0x0a, 0x16, 0x43, 0x52, 0x45, 0x41, 0x54, 0x49, 0x4f, 0x4e, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x53,
	0x55, 0x50, 0x50, 0x4f, 0x52, 0x54, 0x45, 0x44, 0x10, 0x0a, 0x42, 0xf5, 0x01, 0x0a, 0x22, 0x63,
	0x6f, 0x6d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x65, 0x72, 0x72, 0x6f, 0x72,
	0x73, 0x42, 0x1a, 0x43, 0x6f, 0x6e, 0x76, 0x65, 0x72, 0x73, 0x69, 0x6f, 0x6e, 0x41, 0x63, 0x74,
	0x69, 0x6f, 0x6e, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a,
	0x44, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f,
	0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x34, 0x2f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x3b, 0x65,
	0x72, 0x72, 0x6f, 0x72, 0x73, 0xa2, 0x02, 0x03, 0x47, 0x41, 0x41, 0xaa, 0x02, 0x1e, 0x47, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x41, 0x64, 0x73, 0x2e, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41,
	0x64, 0x73, 0x2e, 0x56, 0x34, 0x2e, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x73, 0xca, 0x02, 0x1e, 0x47,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x5c, 0x41, 0x64, 0x73, 0x5c, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x41, 0x64, 0x73, 0x5c, 0x56, 0x34, 0x5c, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x73, 0xea, 0x02, 0x22,
	0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x3a, 0x3a, 0x41, 0x64, 0x73, 0x3a, 0x3a, 0x47, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x3a, 0x3a, 0x56, 0x34, 0x3a, 0x3a, 0x45, 0x72, 0x72, 0x6f,
	0x72, 0x73, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDescOnce sync.Once
	file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDescData = file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDesc
)

func file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDescGZIP() []byte {
	file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDescOnce.Do(func() {
		file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDescData)
	})
	return file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDescData
}

var file_google_ads_googleads_v4_errors_conversion_action_error_proto_enumTypes = make([]protoimpl.EnumInfo, 1)
var file_google_ads_googleads_v4_errors_conversion_action_error_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_ads_googleads_v4_errors_conversion_action_error_proto_goTypes = []interface{}{
	(ConversionActionErrorEnum_ConversionActionError)(0), // 0: google.ads.googleads.v4.errors.ConversionActionErrorEnum.ConversionActionError
	(*ConversionActionErrorEnum)(nil),                    // 1: google.ads.googleads.v4.errors.ConversionActionErrorEnum
}
var file_google_ads_googleads_v4_errors_conversion_action_error_proto_depIdxs = []int32{
	0, // [0:0] is the sub-list for method output_type
	0, // [0:0] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() { file_google_ads_googleads_v4_errors_conversion_action_error_proto_init() }
func file_google_ads_googleads_v4_errors_conversion_action_error_proto_init() {
	if File_google_ads_googleads_v4_errors_conversion_action_error_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_ads_googleads_v4_errors_conversion_action_error_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ConversionActionErrorEnum); i {
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
			RawDescriptor: file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDesc,
			NumEnums:      1,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_ads_googleads_v4_errors_conversion_action_error_proto_goTypes,
		DependencyIndexes: file_google_ads_googleads_v4_errors_conversion_action_error_proto_depIdxs,
		EnumInfos:         file_google_ads_googleads_v4_errors_conversion_action_error_proto_enumTypes,
		MessageInfos:      file_google_ads_googleads_v4_errors_conversion_action_error_proto_msgTypes,
	}.Build()
	File_google_ads_googleads_v4_errors_conversion_action_error_proto = out.File
	file_google_ads_googleads_v4_errors_conversion_action_error_proto_rawDesc = nil
	file_google_ads_googleads_v4_errors_conversion_action_error_proto_goTypes = nil
	file_google_ads_googleads_v4_errors_conversion_action_error_proto_depIdxs = nil
}
