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
// source: google/ads/googleads/v3/enums/month_of_year.proto

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

// Enumerates months of the year, e.g., "January".
type MonthOfYearEnum_MonthOfYear int32

const (
	// Not specified.
	MonthOfYearEnum_UNSPECIFIED MonthOfYearEnum_MonthOfYear = 0
	// The value is unknown in this version.
	MonthOfYearEnum_UNKNOWN MonthOfYearEnum_MonthOfYear = 1
	// January.
	MonthOfYearEnum_JANUARY MonthOfYearEnum_MonthOfYear = 2
	// February.
	MonthOfYearEnum_FEBRUARY MonthOfYearEnum_MonthOfYear = 3
	// March.
	MonthOfYearEnum_MARCH MonthOfYearEnum_MonthOfYear = 4
	// April.
	MonthOfYearEnum_APRIL MonthOfYearEnum_MonthOfYear = 5
	// May.
	MonthOfYearEnum_MAY MonthOfYearEnum_MonthOfYear = 6
	// June.
	MonthOfYearEnum_JUNE MonthOfYearEnum_MonthOfYear = 7
	// July.
	MonthOfYearEnum_JULY MonthOfYearEnum_MonthOfYear = 8
	// August.
	MonthOfYearEnum_AUGUST MonthOfYearEnum_MonthOfYear = 9
	// September.
	MonthOfYearEnum_SEPTEMBER MonthOfYearEnum_MonthOfYear = 10
	// October.
	MonthOfYearEnum_OCTOBER MonthOfYearEnum_MonthOfYear = 11
	// November.
	MonthOfYearEnum_NOVEMBER MonthOfYearEnum_MonthOfYear = 12
	// December.
	MonthOfYearEnum_DECEMBER MonthOfYearEnum_MonthOfYear = 13
)

// Enum value maps for MonthOfYearEnum_MonthOfYear.
var (
	MonthOfYearEnum_MonthOfYear_name = map[int32]string{
		0:  "UNSPECIFIED",
		1:  "UNKNOWN",
		2:  "JANUARY",
		3:  "FEBRUARY",
		4:  "MARCH",
		5:  "APRIL",
		6:  "MAY",
		7:  "JUNE",
		8:  "JULY",
		9:  "AUGUST",
		10: "SEPTEMBER",
		11: "OCTOBER",
		12: "NOVEMBER",
		13: "DECEMBER",
	}
	MonthOfYearEnum_MonthOfYear_value = map[string]int32{
		"UNSPECIFIED": 0,
		"UNKNOWN":     1,
		"JANUARY":     2,
		"FEBRUARY":    3,
		"MARCH":       4,
		"APRIL":       5,
		"MAY":         6,
		"JUNE":        7,
		"JULY":        8,
		"AUGUST":      9,
		"SEPTEMBER":   10,
		"OCTOBER":     11,
		"NOVEMBER":    12,
		"DECEMBER":    13,
	}
)

func (x MonthOfYearEnum_MonthOfYear) Enum() *MonthOfYearEnum_MonthOfYear {
	p := new(MonthOfYearEnum_MonthOfYear)
	*p = x
	return p
}

func (x MonthOfYearEnum_MonthOfYear) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (MonthOfYearEnum_MonthOfYear) Descriptor() protoreflect.EnumDescriptor {
	return file_google_ads_googleads_v3_enums_month_of_year_proto_enumTypes[0].Descriptor()
}

func (MonthOfYearEnum_MonthOfYear) Type() protoreflect.EnumType {
	return &file_google_ads_googleads_v3_enums_month_of_year_proto_enumTypes[0]
}

func (x MonthOfYearEnum_MonthOfYear) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use MonthOfYearEnum_MonthOfYear.Descriptor instead.
func (MonthOfYearEnum_MonthOfYear) EnumDescriptor() ([]byte, []int) {
	return file_google_ads_googleads_v3_enums_month_of_year_proto_rawDescGZIP(), []int{0, 0}
}

// Container for enumeration of months of the year, e.g., "January".
type MonthOfYearEnum struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *MonthOfYearEnum) Reset() {
	*x = MonthOfYearEnum{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v3_enums_month_of_year_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MonthOfYearEnum) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MonthOfYearEnum) ProtoMessage() {}

func (x *MonthOfYearEnum) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v3_enums_month_of_year_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MonthOfYearEnum.ProtoReflect.Descriptor instead.
func (*MonthOfYearEnum) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v3_enums_month_of_year_proto_rawDescGZIP(), []int{0}
}

var File_google_ads_googleads_v3_enums_month_of_year_proto protoreflect.FileDescriptor

var file_google_ads_googleads_v3_enums_month_of_year_proto_rawDesc = []byte{
	0x0a, 0x31, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x33, 0x2f, 0x65, 0x6e, 0x75, 0x6d, 0x73, 0x2f,
	0x6d, 0x6f, 0x6e, 0x74, 0x68, 0x5f, 0x6f, 0x66, 0x5f, 0x79, 0x65, 0x61, 0x72, 0x2e, 0x70, 0x72,
	0x6f, 0x74, 0x6f, 0x12, 0x1d, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x33, 0x2e, 0x65, 0x6e, 0x75,
	0x6d, 0x73, 0x1a, 0x1c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x61,
	0x6e, 0x6e, 0x6f, 0x74, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f,
	0x22, 0xd1, 0x01, 0x0a, 0x0f, 0x4d, 0x6f, 0x6e, 0x74, 0x68, 0x4f, 0x66, 0x59, 0x65, 0x61, 0x72,
	0x45, 0x6e, 0x75, 0x6d, 0x22, 0xbd, 0x01, 0x0a, 0x0b, 0x4d, 0x6f, 0x6e, 0x74, 0x68, 0x4f, 0x66,
	0x59, 0x65, 0x61, 0x72, 0x12, 0x0f, 0x0a, 0x0b, 0x55, 0x4e, 0x53, 0x50, 0x45, 0x43, 0x49, 0x46,
	0x49, 0x45, 0x44, 0x10, 0x00, 0x12, 0x0b, 0x0a, 0x07, 0x55, 0x4e, 0x4b, 0x4e, 0x4f, 0x57, 0x4e,
	0x10, 0x01, 0x12, 0x0b, 0x0a, 0x07, 0x4a, 0x41, 0x4e, 0x55, 0x41, 0x52, 0x59, 0x10, 0x02, 0x12,
	0x0c, 0x0a, 0x08, 0x46, 0x45, 0x42, 0x52, 0x55, 0x41, 0x52, 0x59, 0x10, 0x03, 0x12, 0x09, 0x0a,
	0x05, 0x4d, 0x41, 0x52, 0x43, 0x48, 0x10, 0x04, 0x12, 0x09, 0x0a, 0x05, 0x41, 0x50, 0x52, 0x49,
	0x4c, 0x10, 0x05, 0x12, 0x07, 0x0a, 0x03, 0x4d, 0x41, 0x59, 0x10, 0x06, 0x12, 0x08, 0x0a, 0x04,
	0x4a, 0x55, 0x4e, 0x45, 0x10, 0x07, 0x12, 0x08, 0x0a, 0x04, 0x4a, 0x55, 0x4c, 0x59, 0x10, 0x08,
	0x12, 0x0a, 0x0a, 0x06, 0x41, 0x55, 0x47, 0x55, 0x53, 0x54, 0x10, 0x09, 0x12, 0x0d, 0x0a, 0x09,
	0x53, 0x45, 0x50, 0x54, 0x45, 0x4d, 0x42, 0x45, 0x52, 0x10, 0x0a, 0x12, 0x0b, 0x0a, 0x07, 0x4f,
	0x43, 0x54, 0x4f, 0x42, 0x45, 0x52, 0x10, 0x0b, 0x12, 0x0c, 0x0a, 0x08, 0x4e, 0x4f, 0x56, 0x45,
	0x4d, 0x42, 0x45, 0x52, 0x10, 0x0c, 0x12, 0x0c, 0x0a, 0x08, 0x44, 0x45, 0x43, 0x45, 0x4d, 0x42,
	0x45, 0x52, 0x10, 0x0d, 0x42, 0xe5, 0x01, 0x0a, 0x21, 0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64,
	0x73, 0x2e, 0x76, 0x33, 0x2e, 0x65, 0x6e, 0x75, 0x6d, 0x73, 0x42, 0x10, 0x4d, 0x6f, 0x6e, 0x74,
	0x68, 0x4f, 0x66, 0x59, 0x65, 0x61, 0x72, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a, 0x42,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72,
	0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x61, 0x64, 0x73, 0x2f, 0x76, 0x33, 0x2f, 0x65, 0x6e, 0x75, 0x6d, 0x73, 0x3b, 0x65, 0x6e, 0x75,
	0x6d, 0x73, 0xa2, 0x02, 0x03, 0x47, 0x41, 0x41, 0xaa, 0x02, 0x1d, 0x47, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x2e, 0x41, 0x64, 0x73, 0x2e, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x2e,
	0x56, 0x33, 0x2e, 0x45, 0x6e, 0x75, 0x6d, 0x73, 0xca, 0x02, 0x1d, 0x47, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x5c, 0x41, 0x64, 0x73, 0x5c, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x5c,
	0x56, 0x33, 0x5c, 0x45, 0x6e, 0x75, 0x6d, 0x73, 0xea, 0x02, 0x21, 0x47, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x3a, 0x3a, 0x41, 0x64, 0x73, 0x3a, 0x3a, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64,
	0x73, 0x3a, 0x3a, 0x56, 0x33, 0x3a, 0x3a, 0x45, 0x6e, 0x75, 0x6d, 0x73, 0x62, 0x06, 0x70, 0x72,
	0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_ads_googleads_v3_enums_month_of_year_proto_rawDescOnce sync.Once
	file_google_ads_googleads_v3_enums_month_of_year_proto_rawDescData = file_google_ads_googleads_v3_enums_month_of_year_proto_rawDesc
)

func file_google_ads_googleads_v3_enums_month_of_year_proto_rawDescGZIP() []byte {
	file_google_ads_googleads_v3_enums_month_of_year_proto_rawDescOnce.Do(func() {
		file_google_ads_googleads_v3_enums_month_of_year_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_ads_googleads_v3_enums_month_of_year_proto_rawDescData)
	})
	return file_google_ads_googleads_v3_enums_month_of_year_proto_rawDescData
}

var file_google_ads_googleads_v3_enums_month_of_year_proto_enumTypes = make([]protoimpl.EnumInfo, 1)
var file_google_ads_googleads_v3_enums_month_of_year_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_ads_googleads_v3_enums_month_of_year_proto_goTypes = []interface{}{
	(MonthOfYearEnum_MonthOfYear)(0), // 0: google.ads.googleads.v3.enums.MonthOfYearEnum.MonthOfYear
	(*MonthOfYearEnum)(nil),          // 1: google.ads.googleads.v3.enums.MonthOfYearEnum
}
var file_google_ads_googleads_v3_enums_month_of_year_proto_depIdxs = []int32{
	0, // [0:0] is the sub-list for method output_type
	0, // [0:0] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() { file_google_ads_googleads_v3_enums_month_of_year_proto_init() }
func file_google_ads_googleads_v3_enums_month_of_year_proto_init() {
	if File_google_ads_googleads_v3_enums_month_of_year_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_ads_googleads_v3_enums_month_of_year_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MonthOfYearEnum); i {
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
			RawDescriptor: file_google_ads_googleads_v3_enums_month_of_year_proto_rawDesc,
			NumEnums:      1,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_ads_googleads_v3_enums_month_of_year_proto_goTypes,
		DependencyIndexes: file_google_ads_googleads_v3_enums_month_of_year_proto_depIdxs,
		EnumInfos:         file_google_ads_googleads_v3_enums_month_of_year_proto_enumTypes,
		MessageInfos:      file_google_ads_googleads_v3_enums_month_of_year_proto_msgTypes,
	}.Build()
	File_google_ads_googleads_v3_enums_month_of_year_proto = out.File
	file_google_ads_googleads_v3_enums_month_of_year_proto_rawDesc = nil
	file_google_ads_googleads_v3_enums_month_of_year_proto_goTypes = nil
	file_google_ads_googleads_v3_enums_month_of_year_proto_depIdxs = nil
}
