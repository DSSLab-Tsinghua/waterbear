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
// source: google/cloud/bigquery/storage/v1beta1/read_options.proto

package storage

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

// Options dictating how we read a table.
type TableReadOptions struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Optional. Names of the fields in the table that should be read. If empty,
	// all fields will be read. If the specified field is a nested field, all the
	// sub-fields in the field will be selected. The output field order is
	// unrelated to the order of fields in selected_fields.
	SelectedFields []string `protobuf:"bytes,1,rep,name=selected_fields,json=selectedFields,proto3" json:"selected_fields,omitempty"`
	// Optional. SQL text filtering statement, similar to a WHERE clause in
	// a query. Aggregates are not supported.
	//
	// Examples: "int_field > 5"
	//           "date_field = CAST('2014-9-27' as DATE)"
	//           "nullable_field is not NULL"
	//           "st_equals(geo_field, st_geofromtext("POINT(2, 2)"))"
	//           "numeric_field BETWEEN 1.0 AND 5.0"
	RowRestriction string `protobuf:"bytes,2,opt,name=row_restriction,json=rowRestriction,proto3" json:"row_restriction,omitempty"`
}

func (x *TableReadOptions) Reset() {
	*x = TableReadOptions{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_cloud_bigquery_storage_v1beta1_read_options_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *TableReadOptions) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*TableReadOptions) ProtoMessage() {}

func (x *TableReadOptions) ProtoReflect() protoreflect.Message {
	mi := &file_google_cloud_bigquery_storage_v1beta1_read_options_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use TableReadOptions.ProtoReflect.Descriptor instead.
func (*TableReadOptions) Descriptor() ([]byte, []int) {
	return file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDescGZIP(), []int{0}
}

func (x *TableReadOptions) GetSelectedFields() []string {
	if x != nil {
		return x.SelectedFields
	}
	return nil
}

func (x *TableReadOptions) GetRowRestriction() string {
	if x != nil {
		return x.RowRestriction
	}
	return ""
}

var File_google_cloud_bigquery_storage_v1beta1_read_options_proto protoreflect.FileDescriptor

var file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDesc = []byte{
	0x0a, 0x38, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x63, 0x6c, 0x6f, 0x75, 0x64, 0x2f, 0x62,
	0x69, 0x67, 0x71, 0x75, 0x65, 0x72, 0x79, 0x2f, 0x73, 0x74, 0x6f, 0x72, 0x61, 0x67, 0x65, 0x2f,
	0x76, 0x31, 0x62, 0x65, 0x74, 0x61, 0x31, 0x2f, 0x72, 0x65, 0x61, 0x64, 0x5f, 0x6f, 0x70, 0x74,
	0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x25, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x2e, 0x63, 0x6c, 0x6f, 0x75, 0x64, 0x2e, 0x62, 0x69, 0x67, 0x71, 0x75, 0x65, 0x72,
	0x79, 0x2e, 0x73, 0x74, 0x6f, 0x72, 0x61, 0x67, 0x65, 0x2e, 0x76, 0x31, 0x62, 0x65, 0x74, 0x61,
	0x31, 0x22, 0x64, 0x0a, 0x10, 0x54, 0x61, 0x62, 0x6c, 0x65, 0x52, 0x65, 0x61, 0x64, 0x4f, 0x70,
	0x74, 0x69, 0x6f, 0x6e, 0x73, 0x12, 0x27, 0x0a, 0x0f, 0x73, 0x65, 0x6c, 0x65, 0x63, 0x74, 0x65,
	0x64, 0x5f, 0x66, 0x69, 0x65, 0x6c, 0x64, 0x73, 0x18, 0x01, 0x20, 0x03, 0x28, 0x09, 0x52, 0x0e,
	0x73, 0x65, 0x6c, 0x65, 0x63, 0x74, 0x65, 0x64, 0x46, 0x69, 0x65, 0x6c, 0x64, 0x73, 0x12, 0x27,
	0x0a, 0x0f, 0x72, 0x6f, 0x77, 0x5f, 0x72, 0x65, 0x73, 0x74, 0x72, 0x69, 0x63, 0x74, 0x69, 0x6f,
	0x6e, 0x18, 0x02, 0x20, 0x01, 0x28, 0x09, 0x52, 0x0e, 0x72, 0x6f, 0x77, 0x52, 0x65, 0x73, 0x74,
	0x72, 0x69, 0x63, 0x74, 0x69, 0x6f, 0x6e, 0x42, 0x79, 0x0a, 0x29, 0x63, 0x6f, 0x6d, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x63, 0x6c, 0x6f, 0x75, 0x64, 0x2e, 0x62, 0x69, 0x67, 0x71,
	0x75, 0x65, 0x72, 0x79, 0x2e, 0x73, 0x74, 0x6f, 0x72, 0x61, 0x67, 0x65, 0x2e, 0x76, 0x31, 0x62,
	0x65, 0x74, 0x61, 0x31, 0x5a, 0x4c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c,
	0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f,
	0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x63, 0x6c, 0x6f, 0x75,
	0x64, 0x2f, 0x62, 0x69, 0x67, 0x71, 0x75, 0x65, 0x72, 0x79, 0x2f, 0x73, 0x74, 0x6f, 0x72, 0x61,
	0x67, 0x65, 0x2f, 0x76, 0x31, 0x62, 0x65, 0x74, 0x61, 0x31, 0x3b, 0x73, 0x74, 0x6f, 0x72, 0x61,
	0x67, 0x65, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDescOnce sync.Once
	file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDescData = file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDesc
)

func file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDescGZIP() []byte {
	file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDescOnce.Do(func() {
		file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDescData)
	})
	return file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDescData
}

var file_google_cloud_bigquery_storage_v1beta1_read_options_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_cloud_bigquery_storage_v1beta1_read_options_proto_goTypes = []interface{}{
	(*TableReadOptions)(nil), // 0: google.cloud.bigquery.storage.v1beta1.TableReadOptions
}
var file_google_cloud_bigquery_storage_v1beta1_read_options_proto_depIdxs = []int32{
	0, // [0:0] is the sub-list for method output_type
	0, // [0:0] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() { file_google_cloud_bigquery_storage_v1beta1_read_options_proto_init() }
func file_google_cloud_bigquery_storage_v1beta1_read_options_proto_init() {
	if File_google_cloud_bigquery_storage_v1beta1_read_options_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_cloud_bigquery_storage_v1beta1_read_options_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*TableReadOptions); i {
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
			RawDescriptor: file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_cloud_bigquery_storage_v1beta1_read_options_proto_goTypes,
		DependencyIndexes: file_google_cloud_bigquery_storage_v1beta1_read_options_proto_depIdxs,
		MessageInfos:      file_google_cloud_bigquery_storage_v1beta1_read_options_proto_msgTypes,
	}.Build()
	File_google_cloud_bigquery_storage_v1beta1_read_options_proto = out.File
	file_google_cloud_bigquery_storage_v1beta1_read_options_proto_rawDesc = nil
	file_google_cloud_bigquery_storage_v1beta1_read_options_proto_goTypes = nil
	file_google_cloud_bigquery_storage_v1beta1_read_options_proto_depIdxs = nil
}
