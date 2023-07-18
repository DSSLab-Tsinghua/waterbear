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
// source: google/monitoring/dashboard/v1/text.proto

package dashboard

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

// The format type of the text content.
type Text_Format int32

const (
	// Format is unspecified. Defaults to MARKDOWN.
	Text_FORMAT_UNSPECIFIED Text_Format = 0
	// The text contains Markdown formatting.
	Text_MARKDOWN Text_Format = 1
	// The text contains no special formatting.
	Text_RAW Text_Format = 2
)

// Enum value maps for Text_Format.
var (
	Text_Format_name = map[int32]string{
		0: "FORMAT_UNSPECIFIED",
		1: "MARKDOWN",
		2: "RAW",
	}
	Text_Format_value = map[string]int32{
		"FORMAT_UNSPECIFIED": 0,
		"MARKDOWN":           1,
		"RAW":                2,
	}
)

func (x Text_Format) Enum() *Text_Format {
	p := new(Text_Format)
	*p = x
	return p
}

func (x Text_Format) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (Text_Format) Descriptor() protoreflect.EnumDescriptor {
	return file_google_monitoring_dashboard_v1_text_proto_enumTypes[0].Descriptor()
}

func (Text_Format) Type() protoreflect.EnumType {
	return &file_google_monitoring_dashboard_v1_text_proto_enumTypes[0]
}

func (x Text_Format) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use Text_Format.Descriptor instead.
func (Text_Format) EnumDescriptor() ([]byte, []int) {
	return file_google_monitoring_dashboard_v1_text_proto_rawDescGZIP(), []int{0, 0}
}

// A widget that displays textual content.
type Text struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// The text content to be displayed.
	Content string `protobuf:"bytes,1,opt,name=content,proto3" json:"content,omitempty"`
	// How the text content is formatted.
	Format Text_Format `protobuf:"varint,2,opt,name=format,proto3,enum=google.monitoring.dashboard.v1.Text_Format" json:"format,omitempty"`
}

func (x *Text) Reset() {
	*x = Text{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_monitoring_dashboard_v1_text_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *Text) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*Text) ProtoMessage() {}

func (x *Text) ProtoReflect() protoreflect.Message {
	mi := &file_google_monitoring_dashboard_v1_text_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use Text.ProtoReflect.Descriptor instead.
func (*Text) Descriptor() ([]byte, []int) {
	return file_google_monitoring_dashboard_v1_text_proto_rawDescGZIP(), []int{0}
}

func (x *Text) GetContent() string {
	if x != nil {
		return x.Content
	}
	return ""
}

func (x *Text) GetFormat() Text_Format {
	if x != nil {
		return x.Format
	}
	return Text_FORMAT_UNSPECIFIED
}

var File_google_monitoring_dashboard_v1_text_proto protoreflect.FileDescriptor

var file_google_monitoring_dashboard_v1_text_proto_rawDesc = []byte{
	0x0a, 0x29, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x6d, 0x6f, 0x6e, 0x69, 0x74, 0x6f, 0x72,
	0x69, 0x6e, 0x67, 0x2f, 0x64, 0x61, 0x73, 0x68, 0x62, 0x6f, 0x61, 0x72, 0x64, 0x2f, 0x76, 0x31,
	0x2f, 0x74, 0x65, 0x78, 0x74, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x1e, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x2e, 0x6d, 0x6f, 0x6e, 0x69, 0x74, 0x6f, 0x72, 0x69, 0x6e, 0x67, 0x2e, 0x64,
	0x61, 0x73, 0x68, 0x62, 0x6f, 0x61, 0x72, 0x64, 0x2e, 0x76, 0x31, 0x22, 0x9e, 0x01, 0x0a, 0x04,
	0x54, 0x65, 0x78, 0x74, 0x12, 0x18, 0x0a, 0x07, 0x63, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x18,
	0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x07, 0x63, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x12, 0x43,
	0x0a, 0x06, 0x66, 0x6f, 0x72, 0x6d, 0x61, 0x74, 0x18, 0x02, 0x20, 0x01, 0x28, 0x0e, 0x32, 0x2b,
	0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x6d, 0x6f, 0x6e, 0x69, 0x74, 0x6f, 0x72, 0x69,
	0x6e, 0x67, 0x2e, 0x64, 0x61, 0x73, 0x68, 0x62, 0x6f, 0x61, 0x72, 0x64, 0x2e, 0x76, 0x31, 0x2e,
	0x54, 0x65, 0x78, 0x74, 0x2e, 0x46, 0x6f, 0x72, 0x6d, 0x61, 0x74, 0x52, 0x06, 0x66, 0x6f, 0x72,
	0x6d, 0x61, 0x74, 0x22, 0x37, 0x0a, 0x06, 0x46, 0x6f, 0x72, 0x6d, 0x61, 0x74, 0x12, 0x16, 0x0a,
	0x12, 0x46, 0x4f, 0x52, 0x4d, 0x41, 0x54, 0x5f, 0x55, 0x4e, 0x53, 0x50, 0x45, 0x43, 0x49, 0x46,
	0x49, 0x45, 0x44, 0x10, 0x00, 0x12, 0x0c, 0x0a, 0x08, 0x4d, 0x41, 0x52, 0x4b, 0x44, 0x4f, 0x57,
	0x4e, 0x10, 0x01, 0x12, 0x07, 0x0a, 0x03, 0x52, 0x41, 0x57, 0x10, 0x02, 0x42, 0xa5, 0x01, 0x0a,
	0x22, 0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x6d, 0x6f, 0x6e, 0x69,
	0x74, 0x6f, 0x72, 0x69, 0x6e, 0x67, 0x2e, 0x64, 0x61, 0x73, 0x68, 0x62, 0x6f, 0x61, 0x72, 0x64,
	0x2e, 0x76, 0x31, 0x42, 0x09, 0x54, 0x65, 0x78, 0x74, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01,
	0x5a, 0x47, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e,
	0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x6d, 0x6f, 0x6e, 0x69, 0x74, 0x6f, 0x72, 0x69,
	0x6e, 0x67, 0x2f, 0x64, 0x61, 0x73, 0x68, 0x62, 0x6f, 0x61, 0x72, 0x64, 0x2f, 0x76, 0x31, 0x3b,
	0x64, 0x61, 0x73, 0x68, 0x62, 0x6f, 0x61, 0x72, 0x64, 0xea, 0x02, 0x28, 0x47, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x3a, 0x3a, 0x43, 0x6c, 0x6f, 0x75, 0x64, 0x3a, 0x3a, 0x4d, 0x6f, 0x6e, 0x69, 0x74,
	0x6f, 0x72, 0x69, 0x6e, 0x67, 0x3a, 0x3a, 0x44, 0x61, 0x73, 0x68, 0x62, 0x6f, 0x61, 0x72, 0x64,
	0x3a, 0x3a, 0x56, 0x31, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_monitoring_dashboard_v1_text_proto_rawDescOnce sync.Once
	file_google_monitoring_dashboard_v1_text_proto_rawDescData = file_google_monitoring_dashboard_v1_text_proto_rawDesc
)

func file_google_monitoring_dashboard_v1_text_proto_rawDescGZIP() []byte {
	file_google_monitoring_dashboard_v1_text_proto_rawDescOnce.Do(func() {
		file_google_monitoring_dashboard_v1_text_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_monitoring_dashboard_v1_text_proto_rawDescData)
	})
	return file_google_monitoring_dashboard_v1_text_proto_rawDescData
}

var file_google_monitoring_dashboard_v1_text_proto_enumTypes = make([]protoimpl.EnumInfo, 1)
var file_google_monitoring_dashboard_v1_text_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_monitoring_dashboard_v1_text_proto_goTypes = []interface{}{
	(Text_Format)(0), // 0: google.monitoring.dashboard.v1.Text.Format
	(*Text)(nil),     // 1: google.monitoring.dashboard.v1.Text
}
var file_google_monitoring_dashboard_v1_text_proto_depIdxs = []int32{
	0, // 0: google.monitoring.dashboard.v1.Text.format:type_name -> google.monitoring.dashboard.v1.Text.Format
	1, // [1:1] is the sub-list for method output_type
	1, // [1:1] is the sub-list for method input_type
	1, // [1:1] is the sub-list for extension type_name
	1, // [1:1] is the sub-list for extension extendee
	0, // [0:1] is the sub-list for field type_name
}

func init() { file_google_monitoring_dashboard_v1_text_proto_init() }
func file_google_monitoring_dashboard_v1_text_proto_init() {
	if File_google_monitoring_dashboard_v1_text_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_monitoring_dashboard_v1_text_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*Text); i {
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
			RawDescriptor: file_google_monitoring_dashboard_v1_text_proto_rawDesc,
			NumEnums:      1,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_monitoring_dashboard_v1_text_proto_goTypes,
		DependencyIndexes: file_google_monitoring_dashboard_v1_text_proto_depIdxs,
		EnumInfos:         file_google_monitoring_dashboard_v1_text_proto_enumTypes,
		MessageInfos:      file_google_monitoring_dashboard_v1_text_proto_msgTypes,
	}.Build()
	File_google_monitoring_dashboard_v1_text_proto = out.File
	file_google_monitoring_dashboard_v1_text_proto_rawDesc = nil
	file_google_monitoring_dashboard_v1_text_proto_goTypes = nil
	file_google_monitoring_dashboard_v1_text_proto_depIdxs = nil
}
