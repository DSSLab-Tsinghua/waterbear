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
// source: google/cloud/websecurityscanner/v1/scan_run_warning_trace.proto

package websecurityscanner

import (
	reflect "reflect"
	sync "sync"

	proto "github.com/golang/protobuf/proto"
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

// Output only.
// Defines a warning message code.
// Next id: 6
type ScanRunWarningTrace_Code int32

const (
	// Default value is never used.
	ScanRunWarningTrace_CODE_UNSPECIFIED ScanRunWarningTrace_Code = 0
	// Indicates that a scan discovered an unexpectedly low number of URLs. This
	// is sometimes caused by complex navigation features or by using a single
	// URL for numerous pages.
	ScanRunWarningTrace_INSUFFICIENT_CRAWL_RESULTS ScanRunWarningTrace_Code = 1
	// Indicates that a scan discovered too many URLs to test, or excessive
	// redundant URLs.
	ScanRunWarningTrace_TOO_MANY_CRAWL_RESULTS ScanRunWarningTrace_Code = 2
	// Indicates that too many tests have been generated for the scan. Customer
	// should try reducing the number of starting URLs, increasing the QPS rate,
	// or narrowing down the scope of the scan using the excluded patterns.
	ScanRunWarningTrace_TOO_MANY_FUZZ_TASKS ScanRunWarningTrace_Code = 3
	// Indicates that a scan is blocked by IAP.
	ScanRunWarningTrace_BLOCKED_BY_IAP ScanRunWarningTrace_Code = 4
)

// Enum value maps for ScanRunWarningTrace_Code.
var (
	ScanRunWarningTrace_Code_name = map[int32]string{
		0: "CODE_UNSPECIFIED",
		1: "INSUFFICIENT_CRAWL_RESULTS",
		2: "TOO_MANY_CRAWL_RESULTS",
		3: "TOO_MANY_FUZZ_TASKS",
		4: "BLOCKED_BY_IAP",
	}
	ScanRunWarningTrace_Code_value = map[string]int32{
		"CODE_UNSPECIFIED":           0,
		"INSUFFICIENT_CRAWL_RESULTS": 1,
		"TOO_MANY_CRAWL_RESULTS":     2,
		"TOO_MANY_FUZZ_TASKS":        3,
		"BLOCKED_BY_IAP":             4,
	}
)

func (x ScanRunWarningTrace_Code) Enum() *ScanRunWarningTrace_Code {
	p := new(ScanRunWarningTrace_Code)
	*p = x
	return p
}

func (x ScanRunWarningTrace_Code) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (ScanRunWarningTrace_Code) Descriptor() protoreflect.EnumDescriptor {
	return file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_enumTypes[0].Descriptor()
}

func (ScanRunWarningTrace_Code) Type() protoreflect.EnumType {
	return &file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_enumTypes[0]
}

func (x ScanRunWarningTrace_Code) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use ScanRunWarningTrace_Code.Descriptor instead.
func (ScanRunWarningTrace_Code) EnumDescriptor() ([]byte, []int) {
	return file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDescGZIP(), []int{0, 0}
}

// Output only.
// Defines a warning trace message for ScanRun. Warning traces provide customers
// with useful information that helps make the scanning process more effective.
type ScanRunWarningTrace struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Output only. Indicates the warning code.
	Code ScanRunWarningTrace_Code `protobuf:"varint,1,opt,name=code,proto3,enum=google.cloud.websecurityscanner.v1.ScanRunWarningTrace_Code" json:"code,omitempty"`
}

func (x *ScanRunWarningTrace) Reset() {
	*x = ScanRunWarningTrace{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ScanRunWarningTrace) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ScanRunWarningTrace) ProtoMessage() {}

func (x *ScanRunWarningTrace) ProtoReflect() protoreflect.Message {
	mi := &file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ScanRunWarningTrace.ProtoReflect.Descriptor instead.
func (*ScanRunWarningTrace) Descriptor() ([]byte, []int) {
	return file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDescGZIP(), []int{0}
}

func (x *ScanRunWarningTrace) GetCode() ScanRunWarningTrace_Code {
	if x != nil {
		return x.Code
	}
	return ScanRunWarningTrace_CODE_UNSPECIFIED
}

var File_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto protoreflect.FileDescriptor

var file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDesc = []byte{
	0x0a, 0x3f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x63, 0x6c, 0x6f, 0x75, 0x64, 0x2f, 0x77,
	0x65, 0x62, 0x73, 0x65, 0x63, 0x75, 0x72, 0x69, 0x74, 0x79, 0x73, 0x63, 0x61, 0x6e, 0x6e, 0x65,
	0x72, 0x2f, 0x76, 0x31, 0x2f, 0x73, 0x63, 0x61, 0x6e, 0x5f, 0x72, 0x75, 0x6e, 0x5f, 0x77, 0x61,
	0x72, 0x6e, 0x69, 0x6e, 0x67, 0x5f, 0x74, 0x72, 0x61, 0x63, 0x65, 0x2e, 0x70, 0x72, 0x6f, 0x74,
	0x6f, 0x12, 0x22, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x63, 0x6c, 0x6f, 0x75, 0x64, 0x2e,
	0x77, 0x65, 0x62, 0x73, 0x65, 0x63, 0x75, 0x72, 0x69, 0x74, 0x79, 0x73, 0x63, 0x61, 0x6e, 0x6e,
	0x65, 0x72, 0x2e, 0x76, 0x31, 0x22, 0xef, 0x01, 0x0a, 0x13, 0x53, 0x63, 0x61, 0x6e, 0x52, 0x75,
	0x6e, 0x57, 0x61, 0x72, 0x6e, 0x69, 0x6e, 0x67, 0x54, 0x72, 0x61, 0x63, 0x65, 0x12, 0x50, 0x0a,
	0x04, 0x63, 0x6f, 0x64, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28, 0x0e, 0x32, 0x3c, 0x2e, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x63, 0x6c, 0x6f, 0x75, 0x64, 0x2e, 0x77, 0x65, 0x62, 0x73, 0x65,
	0x63, 0x75, 0x72, 0x69, 0x74, 0x79, 0x73, 0x63, 0x61, 0x6e, 0x6e, 0x65, 0x72, 0x2e, 0x76, 0x31,
	0x2e, 0x53, 0x63, 0x61, 0x6e, 0x52, 0x75, 0x6e, 0x57, 0x61, 0x72, 0x6e, 0x69, 0x6e, 0x67, 0x54,
	0x72, 0x61, 0x63, 0x65, 0x2e, 0x43, 0x6f, 0x64, 0x65, 0x52, 0x04, 0x63, 0x6f, 0x64, 0x65, 0x22,
	0x85, 0x01, 0x0a, 0x04, 0x43, 0x6f, 0x64, 0x65, 0x12, 0x14, 0x0a, 0x10, 0x43, 0x4f, 0x44, 0x45,
	0x5f, 0x55, 0x4e, 0x53, 0x50, 0x45, 0x43, 0x49, 0x46, 0x49, 0x45, 0x44, 0x10, 0x00, 0x12, 0x1e,
	0x0a, 0x1a, 0x49, 0x4e, 0x53, 0x55, 0x46, 0x46, 0x49, 0x43, 0x49, 0x45, 0x4e, 0x54, 0x5f, 0x43,
	0x52, 0x41, 0x57, 0x4c, 0x5f, 0x52, 0x45, 0x53, 0x55, 0x4c, 0x54, 0x53, 0x10, 0x01, 0x12, 0x1a,
	0x0a, 0x16, 0x54, 0x4f, 0x4f, 0x5f, 0x4d, 0x41, 0x4e, 0x59, 0x5f, 0x43, 0x52, 0x41, 0x57, 0x4c,
	0x5f, 0x52, 0x45, 0x53, 0x55, 0x4c, 0x54, 0x53, 0x10, 0x02, 0x12, 0x17, 0x0a, 0x13, 0x54, 0x4f,
	0x4f, 0x5f, 0x4d, 0x41, 0x4e, 0x59, 0x5f, 0x46, 0x55, 0x5a, 0x5a, 0x5f, 0x54, 0x41, 0x53, 0x4b,
	0x53, 0x10, 0x03, 0x12, 0x12, 0x0a, 0x0e, 0x42, 0x4c, 0x4f, 0x43, 0x4b, 0x45, 0x44, 0x5f, 0x42,
	0x59, 0x5f, 0x49, 0x41, 0x50, 0x10, 0x04, 0x42, 0x9a, 0x01, 0x0a, 0x26, 0x63, 0x6f, 0x6d, 0x2e,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x63, 0x6c, 0x6f, 0x75, 0x64, 0x2e, 0x77, 0x65, 0x62,
	0x73, 0x65, 0x63, 0x75, 0x72, 0x69, 0x74, 0x79, 0x73, 0x63, 0x61, 0x6e, 0x6e, 0x65, 0x72, 0x2e,
	0x76, 0x31, 0x42, 0x18, 0x53, 0x63, 0x61, 0x6e, 0x52, 0x75, 0x6e, 0x57, 0x61, 0x72, 0x6e, 0x69,
	0x6e, 0x67, 0x54, 0x72, 0x61, 0x63, 0x65, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a, 0x54,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72,
	0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x63, 0x6c, 0x6f, 0x75, 0x64, 0x2f, 0x77, 0x65, 0x62, 0x73,
	0x65, 0x63, 0x75, 0x72, 0x69, 0x74, 0x79, 0x73, 0x63, 0x61, 0x6e, 0x6e, 0x65, 0x72, 0x2f, 0x76,
	0x31, 0x3b, 0x77, 0x65, 0x62, 0x73, 0x65, 0x63, 0x75, 0x72, 0x69, 0x74, 0x79, 0x73, 0x63, 0x61,
	0x6e, 0x6e, 0x65, 0x72, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDescOnce sync.Once
	file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDescData = file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDesc
)

func file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDescGZIP() []byte {
	file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDescOnce.Do(func() {
		file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDescData)
	})
	return file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDescData
}

var file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_enumTypes = make([]protoimpl.EnumInfo, 1)
var file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_goTypes = []interface{}{
	(ScanRunWarningTrace_Code)(0), // 0: google.cloud.websecurityscanner.v1.ScanRunWarningTrace.Code
	(*ScanRunWarningTrace)(nil),   // 1: google.cloud.websecurityscanner.v1.ScanRunWarningTrace
}
var file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_depIdxs = []int32{
	0, // 0: google.cloud.websecurityscanner.v1.ScanRunWarningTrace.code:type_name -> google.cloud.websecurityscanner.v1.ScanRunWarningTrace.Code
	1, // [1:1] is the sub-list for method output_type
	1, // [1:1] is the sub-list for method input_type
	1, // [1:1] is the sub-list for extension type_name
	1, // [1:1] is the sub-list for extension extendee
	0, // [0:1] is the sub-list for field type_name
}

func init() { file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_init() }
func file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_init() {
	if File_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ScanRunWarningTrace); i {
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
			RawDescriptor: file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDesc,
			NumEnums:      1,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_goTypes,
		DependencyIndexes: file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_depIdxs,
		EnumInfos:         file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_enumTypes,
		MessageInfos:      file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_msgTypes,
	}.Build()
	File_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto = out.File
	file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_rawDesc = nil
	file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_goTypes = nil
	file_google_cloud_websecurityscanner_v1_scan_run_warning_trace_proto_depIdxs = nil
}
