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
// source: google/maps/routes/v1/fallback_info.proto

package routes

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

// Reasons for using fallback response.
type FallbackReason int32

const (
	// No fallback reason specified.
	FallbackReason_FALLBACK_REASON_UNSPECIFIED FallbackReason = 0
	// A server error happened while calculating routes with your preferred
	// routing mode, but we were able to return a result calculated by an
	// alternative mode.
	FallbackReason_SERVER_ERROR FallbackReason = 1
	// We were not able to finish the calculation with your preferred routing mode
	// on time, but we were able to return a result calculated by an alternative
	// mode.
	FallbackReason_LATENCY_EXCEEDED FallbackReason = 2
)

// Enum value maps for FallbackReason.
var (
	FallbackReason_name = map[int32]string{
		0: "FALLBACK_REASON_UNSPECIFIED",
		1: "SERVER_ERROR",
		2: "LATENCY_EXCEEDED",
	}
	FallbackReason_value = map[string]int32{
		"FALLBACK_REASON_UNSPECIFIED": 0,
		"SERVER_ERROR":                1,
		"LATENCY_EXCEEDED":            2,
	}
)

func (x FallbackReason) Enum() *FallbackReason {
	p := new(FallbackReason)
	*p = x
	return p
}

func (x FallbackReason) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (FallbackReason) Descriptor() protoreflect.EnumDescriptor {
	return file_google_maps_routes_v1_fallback_info_proto_enumTypes[0].Descriptor()
}

func (FallbackReason) Type() protoreflect.EnumType {
	return &file_google_maps_routes_v1_fallback_info_proto_enumTypes[0]
}

func (x FallbackReason) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use FallbackReason.Descriptor instead.
func (FallbackReason) EnumDescriptor() ([]byte, []int) {
	return file_google_maps_routes_v1_fallback_info_proto_rawDescGZIP(), []int{0}
}

// Actual routing mode used for returned fallback response.
type FallbackRoutingMode int32

const (
	// Not used.
	FallbackRoutingMode_FALLBACK_ROUTING_MODE_UNSPECIFIED FallbackRoutingMode = 0
	// Indicates the "TRAFFIC_UNAWARE" routing mode was used to compute the
	// response.
	FallbackRoutingMode_FALLBACK_TRAFFIC_UNAWARE FallbackRoutingMode = 1
	// Indicates the "TRAFFIC_AWARE" routing mode was used to compute the
	// response.
	FallbackRoutingMode_FALLBACK_TRAFFIC_AWARE FallbackRoutingMode = 2
)

// Enum value maps for FallbackRoutingMode.
var (
	FallbackRoutingMode_name = map[int32]string{
		0: "FALLBACK_ROUTING_MODE_UNSPECIFIED",
		1: "FALLBACK_TRAFFIC_UNAWARE",
		2: "FALLBACK_TRAFFIC_AWARE",
	}
	FallbackRoutingMode_value = map[string]int32{
		"FALLBACK_ROUTING_MODE_UNSPECIFIED": 0,
		"FALLBACK_TRAFFIC_UNAWARE":          1,
		"FALLBACK_TRAFFIC_AWARE":            2,
	}
)

func (x FallbackRoutingMode) Enum() *FallbackRoutingMode {
	p := new(FallbackRoutingMode)
	*p = x
	return p
}

func (x FallbackRoutingMode) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (FallbackRoutingMode) Descriptor() protoreflect.EnumDescriptor {
	return file_google_maps_routes_v1_fallback_info_proto_enumTypes[1].Descriptor()
}

func (FallbackRoutingMode) Type() protoreflect.EnumType {
	return &file_google_maps_routes_v1_fallback_info_proto_enumTypes[1]
}

func (x FallbackRoutingMode) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use FallbackRoutingMode.Descriptor instead.
func (FallbackRoutingMode) EnumDescriptor() ([]byte, []int) {
	return file_google_maps_routes_v1_fallback_info_proto_rawDescGZIP(), []int{1}
}

// Information related to how and why a fallback result was used. If this field
// is set, then it means the server used a different routing mode from your
// preferred mode as fallback.
type FallbackInfo struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Routing mode used for the response. If fallback was triggered, the mode
	// may be different from routing preference set in the original client
	// request.
	RoutingMode FallbackRoutingMode `protobuf:"varint,1,opt,name=routing_mode,json=routingMode,proto3,enum=google.maps.routes.v1.FallbackRoutingMode" json:"routing_mode,omitempty"`
	// The reason why fallback response was used instead of the original response.
	// This field is only populated when the fallback mode is triggered and the
	// fallback response is returned.
	Reason FallbackReason `protobuf:"varint,2,opt,name=reason,proto3,enum=google.maps.routes.v1.FallbackReason" json:"reason,omitempty"`
}

func (x *FallbackInfo) Reset() {
	*x = FallbackInfo{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_maps_routes_v1_fallback_info_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *FallbackInfo) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*FallbackInfo) ProtoMessage() {}

func (x *FallbackInfo) ProtoReflect() protoreflect.Message {
	mi := &file_google_maps_routes_v1_fallback_info_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use FallbackInfo.ProtoReflect.Descriptor instead.
func (*FallbackInfo) Descriptor() ([]byte, []int) {
	return file_google_maps_routes_v1_fallback_info_proto_rawDescGZIP(), []int{0}
}

func (x *FallbackInfo) GetRoutingMode() FallbackRoutingMode {
	if x != nil {
		return x.RoutingMode
	}
	return FallbackRoutingMode_FALLBACK_ROUTING_MODE_UNSPECIFIED
}

func (x *FallbackInfo) GetReason() FallbackReason {
	if x != nil {
		return x.Reason
	}
	return FallbackReason_FALLBACK_REASON_UNSPECIFIED
}

var File_google_maps_routes_v1_fallback_info_proto protoreflect.FileDescriptor

var file_google_maps_routes_v1_fallback_info_proto_rawDesc = []byte{
	0x0a, 0x29, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x6d, 0x61, 0x70, 0x73, 0x2f, 0x72, 0x6f,
	0x75, 0x74, 0x65, 0x73, 0x2f, 0x76, 0x31, 0x2f, 0x66, 0x61, 0x6c, 0x6c, 0x62, 0x61, 0x63, 0x6b,
	0x5f, 0x69, 0x6e, 0x66, 0x6f, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x15, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x2e, 0x6d, 0x61, 0x70, 0x73, 0x2e, 0x72, 0x6f, 0x75, 0x74, 0x65, 0x73, 0x2e,
	0x76, 0x31, 0x22, 0x9c, 0x01, 0x0a, 0x0c, 0x46, 0x61, 0x6c, 0x6c, 0x62, 0x61, 0x63, 0x6b, 0x49,
	0x6e, 0x66, 0x6f, 0x12, 0x4d, 0x0a, 0x0c, 0x72, 0x6f, 0x75, 0x74, 0x69, 0x6e, 0x67, 0x5f, 0x6d,
	0x6f, 0x64, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28, 0x0e, 0x32, 0x2a, 0x2e, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x2e, 0x6d, 0x61, 0x70, 0x73, 0x2e, 0x72, 0x6f, 0x75, 0x74, 0x65, 0x73, 0x2e, 0x76,
	0x31, 0x2e, 0x46, 0x61, 0x6c, 0x6c, 0x62, 0x61, 0x63, 0x6b, 0x52, 0x6f, 0x75, 0x74, 0x69, 0x6e,
	0x67, 0x4d, 0x6f, 0x64, 0x65, 0x52, 0x0b, 0x72, 0x6f, 0x75, 0x74, 0x69, 0x6e, 0x67, 0x4d, 0x6f,
	0x64, 0x65, 0x12, 0x3d, 0x0a, 0x06, 0x72, 0x65, 0x61, 0x73, 0x6f, 0x6e, 0x18, 0x02, 0x20, 0x01,
	0x28, 0x0e, 0x32, 0x25, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x6d, 0x61, 0x70, 0x73,
	0x2e, 0x72, 0x6f, 0x75, 0x74, 0x65, 0x73, 0x2e, 0x76, 0x31, 0x2e, 0x46, 0x61, 0x6c, 0x6c, 0x62,
	0x61, 0x63, 0x6b, 0x52, 0x65, 0x61, 0x73, 0x6f, 0x6e, 0x52, 0x06, 0x72, 0x65, 0x61, 0x73, 0x6f,
	0x6e, 0x2a, 0x59, 0x0a, 0x0e, 0x46, 0x61, 0x6c, 0x6c, 0x62, 0x61, 0x63, 0x6b, 0x52, 0x65, 0x61,
	0x73, 0x6f, 0x6e, 0x12, 0x1f, 0x0a, 0x1b, 0x46, 0x41, 0x4c, 0x4c, 0x42, 0x41, 0x43, 0x4b, 0x5f,
	0x52, 0x45, 0x41, 0x53, 0x4f, 0x4e, 0x5f, 0x55, 0x4e, 0x53, 0x50, 0x45, 0x43, 0x49, 0x46, 0x49,
	0x45, 0x44, 0x10, 0x00, 0x12, 0x10, 0x0a, 0x0c, 0x53, 0x45, 0x52, 0x56, 0x45, 0x52, 0x5f, 0x45,
	0x52, 0x52, 0x4f, 0x52, 0x10, 0x01, 0x12, 0x14, 0x0a, 0x10, 0x4c, 0x41, 0x54, 0x45, 0x4e, 0x43,
	0x59, 0x5f, 0x45, 0x58, 0x43, 0x45, 0x45, 0x44, 0x45, 0x44, 0x10, 0x02, 0x2a, 0x76, 0x0a, 0x13,
	0x46, 0x61, 0x6c, 0x6c, 0x62, 0x61, 0x63, 0x6b, 0x52, 0x6f, 0x75, 0x74, 0x69, 0x6e, 0x67, 0x4d,
	0x6f, 0x64, 0x65, 0x12, 0x25, 0x0a, 0x21, 0x46, 0x41, 0x4c, 0x4c, 0x42, 0x41, 0x43, 0x4b, 0x5f,
	0x52, 0x4f, 0x55, 0x54, 0x49, 0x4e, 0x47, 0x5f, 0x4d, 0x4f, 0x44, 0x45, 0x5f, 0x55, 0x4e, 0x53,
	0x50, 0x45, 0x43, 0x49, 0x46, 0x49, 0x45, 0x44, 0x10, 0x00, 0x12, 0x1c, 0x0a, 0x18, 0x46, 0x41,
	0x4c, 0x4c, 0x42, 0x41, 0x43, 0x4b, 0x5f, 0x54, 0x52, 0x41, 0x46, 0x46, 0x49, 0x43, 0x5f, 0x55,
	0x4e, 0x41, 0x57, 0x41, 0x52, 0x45, 0x10, 0x01, 0x12, 0x1a, 0x0a, 0x16, 0x46, 0x41, 0x4c, 0x4c,
	0x42, 0x41, 0x43, 0x4b, 0x5f, 0x54, 0x52, 0x41, 0x46, 0x46, 0x49, 0x43, 0x5f, 0x41, 0x57, 0x41,
	0x52, 0x45, 0x10, 0x02, 0x42, 0xa7, 0x01, 0x0a, 0x19, 0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x2e, 0x6d, 0x61, 0x70, 0x73, 0x2e, 0x72, 0x6f, 0x75, 0x74, 0x65, 0x73, 0x2e,
	0x76, 0x31, 0x42, 0x11, 0x46, 0x61, 0x6c, 0x6c, 0x62, 0x61, 0x63, 0x6b, 0x49, 0x6e, 0x66, 0x6f,
	0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a, 0x3b, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e,
	0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72,
	0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x6d,
	0x61, 0x70, 0x73, 0x2f, 0x72, 0x6f, 0x75, 0x74, 0x65, 0x73, 0x2f, 0x76, 0x31, 0x3b, 0x72, 0x6f,
	0x75, 0x74, 0x65, 0x73, 0xf8, 0x01, 0x01, 0xa2, 0x02, 0x04, 0x47, 0x4d, 0x52, 0x53, 0xaa, 0x02,
	0x15, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x4d, 0x61, 0x70, 0x73, 0x2e, 0x52, 0x6f, 0x75,
	0x74, 0x65, 0x73, 0x2e, 0x56, 0x31, 0xca, 0x02, 0x15, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x5c,
	0x4d, 0x61, 0x70, 0x73, 0x5c, 0x52, 0x6f, 0x75, 0x74, 0x65, 0x73, 0x5c, 0x56, 0x31, 0x62, 0x06,
	0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_maps_routes_v1_fallback_info_proto_rawDescOnce sync.Once
	file_google_maps_routes_v1_fallback_info_proto_rawDescData = file_google_maps_routes_v1_fallback_info_proto_rawDesc
)

func file_google_maps_routes_v1_fallback_info_proto_rawDescGZIP() []byte {
	file_google_maps_routes_v1_fallback_info_proto_rawDescOnce.Do(func() {
		file_google_maps_routes_v1_fallback_info_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_maps_routes_v1_fallback_info_proto_rawDescData)
	})
	return file_google_maps_routes_v1_fallback_info_proto_rawDescData
}

var file_google_maps_routes_v1_fallback_info_proto_enumTypes = make([]protoimpl.EnumInfo, 2)
var file_google_maps_routes_v1_fallback_info_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_maps_routes_v1_fallback_info_proto_goTypes = []interface{}{
	(FallbackReason)(0),      // 0: google.maps.routes.v1.FallbackReason
	(FallbackRoutingMode)(0), // 1: google.maps.routes.v1.FallbackRoutingMode
	(*FallbackInfo)(nil),     // 2: google.maps.routes.v1.FallbackInfo
}
var file_google_maps_routes_v1_fallback_info_proto_depIdxs = []int32{
	1, // 0: google.maps.routes.v1.FallbackInfo.routing_mode:type_name -> google.maps.routes.v1.FallbackRoutingMode
	0, // 1: google.maps.routes.v1.FallbackInfo.reason:type_name -> google.maps.routes.v1.FallbackReason
	2, // [2:2] is the sub-list for method output_type
	2, // [2:2] is the sub-list for method input_type
	2, // [2:2] is the sub-list for extension type_name
	2, // [2:2] is the sub-list for extension extendee
	0, // [0:2] is the sub-list for field type_name
}

func init() { file_google_maps_routes_v1_fallback_info_proto_init() }
func file_google_maps_routes_v1_fallback_info_proto_init() {
	if File_google_maps_routes_v1_fallback_info_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_maps_routes_v1_fallback_info_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*FallbackInfo); i {
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
			RawDescriptor: file_google_maps_routes_v1_fallback_info_proto_rawDesc,
			NumEnums:      2,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_maps_routes_v1_fallback_info_proto_goTypes,
		DependencyIndexes: file_google_maps_routes_v1_fallback_info_proto_depIdxs,
		EnumInfos:         file_google_maps_routes_v1_fallback_info_proto_enumTypes,
		MessageInfos:      file_google_maps_routes_v1_fallback_info_proto_msgTypes,
	}.Build()
	File_google_maps_routes_v1_fallback_info_proto = out.File
	file_google_maps_routes_v1_fallback_info_proto_rawDesc = nil
	file_google_maps_routes_v1_fallback_info_proto_goTypes = nil
	file_google_maps_routes_v1_fallback_info_proto_depIdxs = nil
}
