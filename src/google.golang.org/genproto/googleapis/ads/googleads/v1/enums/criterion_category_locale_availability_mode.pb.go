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
// source: google/ads/googleads/v1/enums/criterion_category_locale_availability_mode.proto

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

// Enum containing the possible CriterionCategoryLocaleAvailabilityMode.
type CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode int32

const (
	// Not specified.
	CriterionCategoryLocaleAvailabilityModeEnum_UNSPECIFIED CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode = 0
	// Used for return value only. Represents value unknown in this version.
	CriterionCategoryLocaleAvailabilityModeEnum_UNKNOWN CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode = 1
	// The category is available to campaigns of all locales.
	CriterionCategoryLocaleAvailabilityModeEnum_ALL_LOCALES CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode = 2
	// The category is available to campaigns within a list of countries,
	// regardless of language.
	CriterionCategoryLocaleAvailabilityModeEnum_COUNTRY_AND_ALL_LANGUAGES CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode = 3
	// The category is available to campaigns within a list of languages,
	// regardless of country.
	CriterionCategoryLocaleAvailabilityModeEnum_LANGUAGE_AND_ALL_COUNTRIES CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode = 4
	// The category is available to campaigns within a list of country, language
	// pairs.
	CriterionCategoryLocaleAvailabilityModeEnum_COUNTRY_AND_LANGUAGE CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode = 5
)

// Enum value maps for CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode.
var (
	CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode_name = map[int32]string{
		0: "UNSPECIFIED",
		1: "UNKNOWN",
		2: "ALL_LOCALES",
		3: "COUNTRY_AND_ALL_LANGUAGES",
		4: "LANGUAGE_AND_ALL_COUNTRIES",
		5: "COUNTRY_AND_LANGUAGE",
	}
	CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode_value = map[string]int32{
		"UNSPECIFIED":                0,
		"UNKNOWN":                    1,
		"ALL_LOCALES":                2,
		"COUNTRY_AND_ALL_LANGUAGES":  3,
		"LANGUAGE_AND_ALL_COUNTRIES": 4,
		"COUNTRY_AND_LANGUAGE":       5,
	}
)

func (x CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode) Enum() *CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode {
	p := new(CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode)
	*p = x
	return p
}

func (x CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode) Descriptor() protoreflect.EnumDescriptor {
	return file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_enumTypes[0].Descriptor()
}

func (CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode) Type() protoreflect.EnumType {
	return &file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_enumTypes[0]
}

func (x CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode.Descriptor instead.
func (CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode) EnumDescriptor() ([]byte, []int) {
	return file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDescGZIP(), []int{0, 0}
}

// Describes locale availability mode for a criterion availability - whether
// it's available globally, or a particular country with all languages, or a
// particular language with all countries, or a country-language pair.
type CriterionCategoryLocaleAvailabilityModeEnum struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *CriterionCategoryLocaleAvailabilityModeEnum) Reset() {
	*x = CriterionCategoryLocaleAvailabilityModeEnum{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *CriterionCategoryLocaleAvailabilityModeEnum) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*CriterionCategoryLocaleAvailabilityModeEnum) ProtoMessage() {}

func (x *CriterionCategoryLocaleAvailabilityModeEnum) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use CriterionCategoryLocaleAvailabilityModeEnum.ProtoReflect.Descriptor instead.
func (*CriterionCategoryLocaleAvailabilityModeEnum) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDescGZIP(), []int{0}
}

var File_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto protoreflect.FileDescriptor

var file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDesc = []byte{
	0x0a, 0x4f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x31, 0x2f, 0x65, 0x6e, 0x75, 0x6d, 0x73, 0x2f,
	0x63, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x5f, 0x63, 0x61, 0x74, 0x65, 0x67, 0x6f,
	0x72, 0x79, 0x5f, 0x6c, 0x6f, 0x63, 0x61, 0x6c, 0x65, 0x5f, 0x61, 0x76, 0x61, 0x69, 0x6c, 0x61,
	0x62, 0x69, 0x6c, 0x69, 0x74, 0x79, 0x5f, 0x6d, 0x6f, 0x64, 0x65, 0x2e, 0x70, 0x72, 0x6f, 0x74,
	0x6f, 0x12, 0x1d, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x31, 0x2e, 0x65, 0x6e, 0x75, 0x6d, 0x73,
	0x1a, 0x1c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x61, 0x6e, 0x6e,
	0x6f, 0x74, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22, 0xe1,
	0x01, 0x0a, 0x2b, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x43, 0x61, 0x74, 0x65,
	0x67, 0x6f, 0x72, 0x79, 0x4c, 0x6f, 0x63, 0x61, 0x6c, 0x65, 0x41, 0x76, 0x61, 0x69, 0x6c, 0x61,
	0x62, 0x69, 0x6c, 0x69, 0x74, 0x79, 0x4d, 0x6f, 0x64, 0x65, 0x45, 0x6e, 0x75, 0x6d, 0x22, 0xb1,
	0x01, 0x0a, 0x27, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x43, 0x61, 0x74, 0x65,
	0x67, 0x6f, 0x72, 0x79, 0x4c, 0x6f, 0x63, 0x61, 0x6c, 0x65, 0x41, 0x76, 0x61, 0x69, 0x6c, 0x61,
	0x62, 0x69, 0x6c, 0x69, 0x74, 0x79, 0x4d, 0x6f, 0x64, 0x65, 0x12, 0x0f, 0x0a, 0x0b, 0x55, 0x4e,
	0x53, 0x50, 0x45, 0x43, 0x49, 0x46, 0x49, 0x45, 0x44, 0x10, 0x00, 0x12, 0x0b, 0x0a, 0x07, 0x55,
	0x4e, 0x4b, 0x4e, 0x4f, 0x57, 0x4e, 0x10, 0x01, 0x12, 0x0f, 0x0a, 0x0b, 0x41, 0x4c, 0x4c, 0x5f,
	0x4c, 0x4f, 0x43, 0x41, 0x4c, 0x45, 0x53, 0x10, 0x02, 0x12, 0x1d, 0x0a, 0x19, 0x43, 0x4f, 0x55,
	0x4e, 0x54, 0x52, 0x59, 0x5f, 0x41, 0x4e, 0x44, 0x5f, 0x41, 0x4c, 0x4c, 0x5f, 0x4c, 0x41, 0x4e,
	0x47, 0x55, 0x41, 0x47, 0x45, 0x53, 0x10, 0x03, 0x12, 0x1e, 0x0a, 0x1a, 0x4c, 0x41, 0x4e, 0x47,
	0x55, 0x41, 0x47, 0x45, 0x5f, 0x41, 0x4e, 0x44, 0x5f, 0x41, 0x4c, 0x4c, 0x5f, 0x43, 0x4f, 0x55,
	0x4e, 0x54, 0x52, 0x49, 0x45, 0x53, 0x10, 0x04, 0x12, 0x18, 0x0a, 0x14, 0x43, 0x4f, 0x55, 0x4e,
	0x54, 0x52, 0x59, 0x5f, 0x41, 0x4e, 0x44, 0x5f, 0x4c, 0x41, 0x4e, 0x47, 0x55, 0x41, 0x47, 0x45,
	0x10, 0x05, 0x42, 0x81, 0x02, 0x0a, 0x21, 0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e,
	0x76, 0x31, 0x2e, 0x65, 0x6e, 0x75, 0x6d, 0x73, 0x42, 0x2c, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72,
	0x69, 0x6f, 0x6e, 0x43, 0x61, 0x74, 0x65, 0x67, 0x6f, 0x72, 0x79, 0x4c, 0x6f, 0x63, 0x61, 0x6c,
	0x65, 0x41, 0x76, 0x61, 0x69, 0x6c, 0x61, 0x62, 0x69, 0x6c, 0x69, 0x74, 0x79, 0x4d, 0x6f, 0x64,
	0x65, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a, 0x42, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70,
	0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f,
	0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x31,
	0x2f, 0x65, 0x6e, 0x75, 0x6d, 0x73, 0x3b, 0x65, 0x6e, 0x75, 0x6d, 0x73, 0xa2, 0x02, 0x03, 0x47,
	0x41, 0x41, 0xaa, 0x02, 0x1d, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x41, 0x64, 0x73, 0x2e,
	0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x2e, 0x56, 0x31, 0x2e, 0x45, 0x6e, 0x75,
	0x6d, 0x73, 0xca, 0x02, 0x1d, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x5c, 0x41, 0x64, 0x73, 0x5c,
	0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x5c, 0x56, 0x31, 0x5c, 0x45, 0x6e, 0x75,
	0x6d, 0x73, 0xea, 0x02, 0x21, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x3a, 0x3a, 0x41, 0x64, 0x73,
	0x3a, 0x3a, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x3a, 0x3a, 0x56, 0x31, 0x3a,
	0x3a, 0x45, 0x6e, 0x75, 0x6d, 0x73, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDescOnce sync.Once
	file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDescData = file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDesc
)

func file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDescGZIP() []byte {
	file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDescOnce.Do(func() {
		file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDescData)
	})
	return file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDescData
}

var file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_enumTypes = make([]protoimpl.EnumInfo, 1)
var file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_goTypes = []interface{}{
	(CriterionCategoryLocaleAvailabilityModeEnum_CriterionCategoryLocaleAvailabilityMode)(0), // 0: google.ads.googleads.v1.enums.CriterionCategoryLocaleAvailabilityModeEnum.CriterionCategoryLocaleAvailabilityMode
	(*CriterionCategoryLocaleAvailabilityModeEnum)(nil),                                      // 1: google.ads.googleads.v1.enums.CriterionCategoryLocaleAvailabilityModeEnum
}
var file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_depIdxs = []int32{
	0, // [0:0] is the sub-list for method output_type
	0, // [0:0] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() {
	file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_init()
}
func file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_init() {
	if File_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*CriterionCategoryLocaleAvailabilityModeEnum); i {
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
			RawDescriptor: file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDesc,
			NumEnums:      1,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_goTypes,
		DependencyIndexes: file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_depIdxs,
		EnumInfos:         file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_enumTypes,
		MessageInfos:      file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_msgTypes,
	}.Build()
	File_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto = out.File
	file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_rawDesc = nil
	file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_goTypes = nil
	file_google_ads_googleads_v1_enums_criterion_category_locale_availability_mode_proto_depIdxs = nil
}
