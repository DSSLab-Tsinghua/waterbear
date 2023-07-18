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
// source: google/ads/googleads/v3/enums/data_driven_model_status.proto

package enums

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

// Enumerates data driven model statuses.
type DataDrivenModelStatusEnum_DataDrivenModelStatus int32

const (
	// Not specified.
	DataDrivenModelStatusEnum_UNSPECIFIED DataDrivenModelStatusEnum_DataDrivenModelStatus = 0
	// Used for return value only. Represents value unknown in this version.
	DataDrivenModelStatusEnum_UNKNOWN DataDrivenModelStatusEnum_DataDrivenModelStatus = 1
	// The data driven model is available.
	DataDrivenModelStatusEnum_AVAILABLE DataDrivenModelStatusEnum_DataDrivenModelStatus = 2
	// The data driven model is stale. It hasn't been updated for at least 7
	// days. It is still being used, but will become expired if it does not get
	// updated for 30 days.
	DataDrivenModelStatusEnum_STALE DataDrivenModelStatusEnum_DataDrivenModelStatus = 3
	// The data driven model expired. It hasn't been updated for at least 30
	// days and cannot be used. Most commonly this is because there hasn't been
	// the required number of events in a recent 30-day period.
	DataDrivenModelStatusEnum_EXPIRED DataDrivenModelStatusEnum_DataDrivenModelStatus = 4
	// The data driven model has never been generated. Most commonly this is
	// because there has never been the required number of events in any 30-day
	// period.
	DataDrivenModelStatusEnum_NEVER_GENERATED DataDrivenModelStatusEnum_DataDrivenModelStatus = 5
)

// Enum value maps for DataDrivenModelStatusEnum_DataDrivenModelStatus.
var (
	DataDrivenModelStatusEnum_DataDrivenModelStatus_name = map[int32]string{
		0: "UNSPECIFIED",
		1: "UNKNOWN",
		2: "AVAILABLE",
		3: "STALE",
		4: "EXPIRED",
		5: "NEVER_GENERATED",
	}
	DataDrivenModelStatusEnum_DataDrivenModelStatus_value = map[string]int32{
		"UNSPECIFIED":     0,
		"UNKNOWN":         1,
		"AVAILABLE":       2,
		"STALE":           3,
		"EXPIRED":         4,
		"NEVER_GENERATED": 5,
	}
)

func (x DataDrivenModelStatusEnum_DataDrivenModelStatus) Enum() *DataDrivenModelStatusEnum_DataDrivenModelStatus {
	p := new(DataDrivenModelStatusEnum_DataDrivenModelStatus)
	*p = x
	return p
}

func (x DataDrivenModelStatusEnum_DataDrivenModelStatus) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (DataDrivenModelStatusEnum_DataDrivenModelStatus) Descriptor() protoreflect.EnumDescriptor {
	return file_google_ads_googleads_v3_enums_data_driven_model_status_proto_enumTypes[0].Descriptor()
}

func (DataDrivenModelStatusEnum_DataDrivenModelStatus) Type() protoreflect.EnumType {
	return &file_google_ads_googleads_v3_enums_data_driven_model_status_proto_enumTypes[0]
}

func (x DataDrivenModelStatusEnum_DataDrivenModelStatus) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use DataDrivenModelStatusEnum_DataDrivenModelStatus.Descriptor instead.
func (DataDrivenModelStatusEnum_DataDrivenModelStatus) EnumDescriptor() ([]byte, []int) {
	return file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDescGZIP(), []int{0, 0}
}

// Container for enum indicating data driven model status.
type DataDrivenModelStatusEnum struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *DataDrivenModelStatusEnum) Reset() {
	*x = DataDrivenModelStatusEnum{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v3_enums_data_driven_model_status_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *DataDrivenModelStatusEnum) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*DataDrivenModelStatusEnum) ProtoMessage() {}

func (x *DataDrivenModelStatusEnum) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v3_enums_data_driven_model_status_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use DataDrivenModelStatusEnum.ProtoReflect.Descriptor instead.
func (*DataDrivenModelStatusEnum) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDescGZIP(), []int{0}
}

var File_google_ads_googleads_v3_enums_data_driven_model_status_proto protoreflect.FileDescriptor

var file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDesc = []byte{
	0x0a, 0x3c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x33, 0x2f, 0x65, 0x6e, 0x75, 0x6d, 0x73, 0x2f,
	0x64, 0x61, 0x74, 0x61, 0x5f, 0x64, 0x72, 0x69, 0x76, 0x65, 0x6e, 0x5f, 0x6d, 0x6f, 0x64, 0x65,
	0x6c, 0x5f, 0x73, 0x74, 0x61, 0x74, 0x75, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x1d,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x33, 0x2e, 0x65, 0x6e, 0x75, 0x6d, 0x73, 0x1a, 0x1c, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x61, 0x6e, 0x6e, 0x6f, 0x74, 0x61,
	0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22, 0x8e, 0x01, 0x0a, 0x19,
	0x44, 0x61, 0x74, 0x61, 0x44, 0x72, 0x69, 0x76, 0x65, 0x6e, 0x4d, 0x6f, 0x64, 0x65, 0x6c, 0x53,
	0x74, 0x61, 0x74, 0x75, 0x73, 0x45, 0x6e, 0x75, 0x6d, 0x22, 0x71, 0x0a, 0x15, 0x44, 0x61, 0x74,
	0x61, 0x44, 0x72, 0x69, 0x76, 0x65, 0x6e, 0x4d, 0x6f, 0x64, 0x65, 0x6c, 0x53, 0x74, 0x61, 0x74,
	0x75, 0x73, 0x12, 0x0f, 0x0a, 0x0b, 0x55, 0x4e, 0x53, 0x50, 0x45, 0x43, 0x49, 0x46, 0x49, 0x45,
	0x44, 0x10, 0x00, 0x12, 0x0b, 0x0a, 0x07, 0x55, 0x4e, 0x4b, 0x4e, 0x4f, 0x57, 0x4e, 0x10, 0x01,
	0x12, 0x0d, 0x0a, 0x09, 0x41, 0x56, 0x41, 0x49, 0x4c, 0x41, 0x42, 0x4c, 0x45, 0x10, 0x02, 0x12,
	0x09, 0x0a, 0x05, 0x53, 0x54, 0x41, 0x4c, 0x45, 0x10, 0x03, 0x12, 0x0b, 0x0a, 0x07, 0x45, 0x58,
	0x50, 0x49, 0x52, 0x45, 0x44, 0x10, 0x04, 0x12, 0x13, 0x0a, 0x0f, 0x4e, 0x45, 0x56, 0x45, 0x52,
	0x5f, 0x47, 0x45, 0x4e, 0x45, 0x52, 0x41, 0x54, 0x45, 0x44, 0x10, 0x05, 0x42, 0xef, 0x01, 0x0a,
	0x21, 0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x33, 0x2e, 0x65, 0x6e, 0x75,
	0x6d, 0x73, 0x42, 0x1a, 0x44, 0x61, 0x74, 0x61, 0x44, 0x72, 0x69, 0x76, 0x65, 0x6e, 0x4d, 0x6f,
	0x64, 0x65, 0x6c, 0x53, 0x74, 0x61, 0x74, 0x75, 0x73, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01,
	0x5a, 0x42, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e,
	0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x33, 0x2f, 0x65, 0x6e, 0x75, 0x6d, 0x73, 0x3b, 0x65,
	0x6e, 0x75, 0x6d, 0x73, 0xa2, 0x02, 0x03, 0x47, 0x41, 0x41, 0xaa, 0x02, 0x1d, 0x47, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x2e, 0x41, 0x64, 0x73, 0x2e, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64,
	0x73, 0x2e, 0x56, 0x33, 0x2e, 0x45, 0x6e, 0x75, 0x6d, 0x73, 0xca, 0x02, 0x1d, 0x47, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x5c, 0x41, 0x64, 0x73, 0x5c, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64,
	0x73, 0x5c, 0x56, 0x33, 0x5c, 0x45, 0x6e, 0x75, 0x6d, 0x73, 0xea, 0x02, 0x21, 0x47, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x3a, 0x3a, 0x41, 0x64, 0x73, 0x3a, 0x3a, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x41, 0x64, 0x73, 0x3a, 0x3a, 0x56, 0x33, 0x3a, 0x3a, 0x45, 0x6e, 0x75, 0x6d, 0x73, 0x62, 0x06,
	0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDescOnce sync.Once
	file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDescData = file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDesc
)

func file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDescGZIP() []byte {
	file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDescOnce.Do(func() {
		file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDescData)
	})
	return file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDescData
}

var file_google_ads_googleads_v3_enums_data_driven_model_status_proto_enumTypes = make([]protoimpl.EnumInfo, 1)
var file_google_ads_googleads_v3_enums_data_driven_model_status_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_ads_googleads_v3_enums_data_driven_model_status_proto_goTypes = []interface{}{
	(DataDrivenModelStatusEnum_DataDrivenModelStatus)(0), // 0: google.ads.googleads.v3.enums.DataDrivenModelStatusEnum.DataDrivenModelStatus
	(*DataDrivenModelStatusEnum)(nil),                    // 1: google.ads.googleads.v3.enums.DataDrivenModelStatusEnum
}
var file_google_ads_googleads_v3_enums_data_driven_model_status_proto_depIdxs = []int32{
	0, // [0:0] is the sub-list for method output_type
	0, // [0:0] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() { file_google_ads_googleads_v3_enums_data_driven_model_status_proto_init() }
func file_google_ads_googleads_v3_enums_data_driven_model_status_proto_init() {
	if File_google_ads_googleads_v3_enums_data_driven_model_status_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_ads_googleads_v3_enums_data_driven_model_status_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*DataDrivenModelStatusEnum); i {
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
			RawDescriptor: file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDesc,
			NumEnums:      1,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_ads_googleads_v3_enums_data_driven_model_status_proto_goTypes,
		DependencyIndexes: file_google_ads_googleads_v3_enums_data_driven_model_status_proto_depIdxs,
		EnumInfos:         file_google_ads_googleads_v3_enums_data_driven_model_status_proto_enumTypes,
		MessageInfos:      file_google_ads_googleads_v3_enums_data_driven_model_status_proto_msgTypes,
	}.Build()
	File_google_ads_googleads_v3_enums_data_driven_model_status_proto = out.File
	file_google_ads_googleads_v3_enums_data_driven_model_status_proto_rawDesc = nil
	file_google_ads_googleads_v3_enums_data_driven_model_status_proto_goTypes = nil
	file_google_ads_googleads_v3_enums_data_driven_model_status_proto_depIdxs = nil
}
