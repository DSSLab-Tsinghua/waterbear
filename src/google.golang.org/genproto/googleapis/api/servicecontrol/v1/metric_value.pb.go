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
// source: google/api/servicecontrol/v1/metric_value.proto

package servicecontrol

import (
	reflect "reflect"
	sync "sync"

	proto "github.com/golang/protobuf/proto"
	timestamp "github.com/golang/protobuf/ptypes/timestamp"
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

// Represents a single metric value.
type MetricValue struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// The labels describing the metric value.
	// See comments on
	// [google.api.servicecontrol.v1.Operation.labels][google.api.servicecontrol.v1.Operation.labels]
	// for the overriding relationship. Note that this map must not contain
	// monitored resource labels.
	Labels map[string]string `protobuf:"bytes,1,rep,name=labels,proto3" json:"labels,omitempty" protobuf_key:"bytes,1,opt,name=key,proto3" protobuf_val:"bytes,2,opt,name=value,proto3"`
	// The start of the time period over which this metric value's measurement
	// applies. The time period has different semantics for different metric
	// types (cumulative, delta, and gauge). See the metric definition
	// documentation in the service configuration for details.
	StartTime *timestamp.Timestamp `protobuf:"bytes,2,opt,name=start_time,json=startTime,proto3" json:"start_time,omitempty"`
	// The end of the time period over which this metric value's measurement
	// applies.
	EndTime *timestamp.Timestamp `protobuf:"bytes,3,opt,name=end_time,json=endTime,proto3" json:"end_time,omitempty"`
	// The value. The type of value used in the request must
	// agree with the metric definition in the service configuration, otherwise
	// the MetricValue is rejected.
	//
	// Types that are assignable to Value:
	//	*MetricValue_BoolValue
	//	*MetricValue_Int64Value
	//	*MetricValue_DoubleValue
	//	*MetricValue_StringValue
	//	*MetricValue_DistributionValue
	Value isMetricValue_Value `protobuf_oneof:"value"`
}

func (x *MetricValue) Reset() {
	*x = MetricValue{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_api_servicecontrol_v1_metric_value_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MetricValue) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MetricValue) ProtoMessage() {}

func (x *MetricValue) ProtoReflect() protoreflect.Message {
	mi := &file_google_api_servicecontrol_v1_metric_value_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MetricValue.ProtoReflect.Descriptor instead.
func (*MetricValue) Descriptor() ([]byte, []int) {
	return file_google_api_servicecontrol_v1_metric_value_proto_rawDescGZIP(), []int{0}
}

func (x *MetricValue) GetLabels() map[string]string {
	if x != nil {
		return x.Labels
	}
	return nil
}

func (x *MetricValue) GetStartTime() *timestamp.Timestamp {
	if x != nil {
		return x.StartTime
	}
	return nil
}

func (x *MetricValue) GetEndTime() *timestamp.Timestamp {
	if x != nil {
		return x.EndTime
	}
	return nil
}

func (m *MetricValue) GetValue() isMetricValue_Value {
	if m != nil {
		return m.Value
	}
	return nil
}

func (x *MetricValue) GetBoolValue() bool {
	if x, ok := x.GetValue().(*MetricValue_BoolValue); ok {
		return x.BoolValue
	}
	return false
}

func (x *MetricValue) GetInt64Value() int64 {
	if x, ok := x.GetValue().(*MetricValue_Int64Value); ok {
		return x.Int64Value
	}
	return 0
}

func (x *MetricValue) GetDoubleValue() float64 {
	if x, ok := x.GetValue().(*MetricValue_DoubleValue); ok {
		return x.DoubleValue
	}
	return 0
}

func (x *MetricValue) GetStringValue() string {
	if x, ok := x.GetValue().(*MetricValue_StringValue); ok {
		return x.StringValue
	}
	return ""
}

func (x *MetricValue) GetDistributionValue() *Distribution {
	if x, ok := x.GetValue().(*MetricValue_DistributionValue); ok {
		return x.DistributionValue
	}
	return nil
}

type isMetricValue_Value interface {
	isMetricValue_Value()
}

type MetricValue_BoolValue struct {
	// A boolean value.
	BoolValue bool `protobuf:"varint,4,opt,name=bool_value,json=boolValue,proto3,oneof"`
}

type MetricValue_Int64Value struct {
	// A signed 64-bit integer value.
	Int64Value int64 `protobuf:"varint,5,opt,name=int64_value,json=int64Value,proto3,oneof"`
}

type MetricValue_DoubleValue struct {
	// A double precision floating point value.
	DoubleValue float64 `protobuf:"fixed64,6,opt,name=double_value,json=doubleValue,proto3,oneof"`
}

type MetricValue_StringValue struct {
	// A text string value.
	StringValue string `protobuf:"bytes,7,opt,name=string_value,json=stringValue,proto3,oneof"`
}

type MetricValue_DistributionValue struct {
	// A distribution value.
	DistributionValue *Distribution `protobuf:"bytes,8,opt,name=distribution_value,json=distributionValue,proto3,oneof"`
}

func (*MetricValue_BoolValue) isMetricValue_Value() {}

func (*MetricValue_Int64Value) isMetricValue_Value() {}

func (*MetricValue_DoubleValue) isMetricValue_Value() {}

func (*MetricValue_StringValue) isMetricValue_Value() {}

func (*MetricValue_DistributionValue) isMetricValue_Value() {}

// Represents a set of metric values in the same metric.
// Each metric value in the set should have a unique combination of start time,
// end time, and label values.
type MetricValueSet struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// The metric name defined in the service configuration.
	MetricName string `protobuf:"bytes,1,opt,name=metric_name,json=metricName,proto3" json:"metric_name,omitempty"`
	// The values in this metric.
	MetricValues []*MetricValue `protobuf:"bytes,2,rep,name=metric_values,json=metricValues,proto3" json:"metric_values,omitempty"`
}

func (x *MetricValueSet) Reset() {
	*x = MetricValueSet{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_api_servicecontrol_v1_metric_value_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MetricValueSet) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MetricValueSet) ProtoMessage() {}

func (x *MetricValueSet) ProtoReflect() protoreflect.Message {
	mi := &file_google_api_servicecontrol_v1_metric_value_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MetricValueSet.ProtoReflect.Descriptor instead.
func (*MetricValueSet) Descriptor() ([]byte, []int) {
	return file_google_api_servicecontrol_v1_metric_value_proto_rawDescGZIP(), []int{1}
}

func (x *MetricValueSet) GetMetricName() string {
	if x != nil {
		return x.MetricName
	}
	return ""
}

func (x *MetricValueSet) GetMetricValues() []*MetricValue {
	if x != nil {
		return x.MetricValues
	}
	return nil
}

var File_google_api_servicecontrol_v1_metric_value_proto protoreflect.FileDescriptor

var file_google_api_servicecontrol_v1_metric_value_proto_rawDesc = []byte{
	0x0a, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x73, 0x65, 0x72,
	0x76, 0x69, 0x63, 0x65, 0x63, 0x6f, 0x6e, 0x74, 0x72, 0x6f, 0x6c, 0x2f, 0x76, 0x31, 0x2f, 0x6d,
	0x65, 0x74, 0x72, 0x69, 0x63, 0x5f, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x2e, 0x70, 0x72, 0x6f, 0x74,
	0x6f, 0x12, 0x1c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x73, 0x65,
	0x72, 0x76, 0x69, 0x63, 0x65, 0x63, 0x6f, 0x6e, 0x74, 0x72, 0x6f, 0x6c, 0x2e, 0x76, 0x31, 0x1a,
	0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x73, 0x65, 0x72, 0x76,
	0x69, 0x63, 0x65, 0x63, 0x6f, 0x6e, 0x74, 0x72, 0x6f, 0x6c, 0x2f, 0x76, 0x31, 0x2f, 0x64, 0x69,
	0x73, 0x74, 0x72, 0x69, 0x62, 0x75, 0x74, 0x69, 0x6f, 0x6e, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f,
	0x1a, 0x1f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x62, 0x75,
	0x66, 0x2f, 0x74, 0x69, 0x6d, 0x65, 0x73, 0x74, 0x61, 0x6d, 0x70, 0x2e, 0x70, 0x72, 0x6f, 0x74,
	0x6f, 0x22, 0xfd, 0x03, 0x0a, 0x0b, 0x4d, 0x65, 0x74, 0x72, 0x69, 0x63, 0x56, 0x61, 0x6c, 0x75,
	0x65, 0x12, 0x4d, 0x0a, 0x06, 0x6c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x18, 0x01, 0x20, 0x03, 0x28,
	0x0b, 0x32, 0x35, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x73,
	0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x63, 0x6f, 0x6e, 0x74, 0x72, 0x6f, 0x6c, 0x2e, 0x76, 0x31,
	0x2e, 0x4d, 0x65, 0x74, 0x72, 0x69, 0x63, 0x56, 0x61, 0x6c, 0x75, 0x65, 0x2e, 0x4c, 0x61, 0x62,
	0x65, 0x6c, 0x73, 0x45, 0x6e, 0x74, 0x72, 0x79, 0x52, 0x06, 0x6c, 0x61, 0x62, 0x65, 0x6c, 0x73,
	0x12, 0x39, 0x0a, 0x0a, 0x73, 0x74, 0x61, 0x72, 0x74, 0x5f, 0x74, 0x69, 0x6d, 0x65, 0x18, 0x02,
	0x20, 0x01, 0x28, 0x0b, 0x32, 0x1a, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x70, 0x72,
	0x6f, 0x74, 0x6f, 0x62, 0x75, 0x66, 0x2e, 0x54, 0x69, 0x6d, 0x65, 0x73, 0x74, 0x61, 0x6d, 0x70,
	0x52, 0x09, 0x73, 0x74, 0x61, 0x72, 0x74, 0x54, 0x69, 0x6d, 0x65, 0x12, 0x35, 0x0a, 0x08, 0x65,
	0x6e, 0x64, 0x5f, 0x74, 0x69, 0x6d, 0x65, 0x18, 0x03, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x1a, 0x2e,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x62, 0x75, 0x66, 0x2e,
	0x54, 0x69, 0x6d, 0x65, 0x73, 0x74, 0x61, 0x6d, 0x70, 0x52, 0x07, 0x65, 0x6e, 0x64, 0x54, 0x69,
	0x6d, 0x65, 0x12, 0x1f, 0x0a, 0x0a, 0x62, 0x6f, 0x6f, 0x6c, 0x5f, 0x76, 0x61, 0x6c, 0x75, 0x65,
	0x18, 0x04, 0x20, 0x01, 0x28, 0x08, 0x48, 0x00, 0x52, 0x09, 0x62, 0x6f, 0x6f, 0x6c, 0x56, 0x61,
	0x6c, 0x75, 0x65, 0x12, 0x21, 0x0a, 0x0b, 0x69, 0x6e, 0x74, 0x36, 0x34, 0x5f, 0x76, 0x61, 0x6c,
	0x75, 0x65, 0x18, 0x05, 0x20, 0x01, 0x28, 0x03, 0x48, 0x00, 0x52, 0x0a, 0x69, 0x6e, 0x74, 0x36,
	0x34, 0x56, 0x61, 0x6c, 0x75, 0x65, 0x12, 0x23, 0x0a, 0x0c, 0x64, 0x6f, 0x75, 0x62, 0x6c, 0x65,
	0x5f, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x18, 0x06, 0x20, 0x01, 0x28, 0x01, 0x48, 0x00, 0x52, 0x0b,
	0x64, 0x6f, 0x75, 0x62, 0x6c, 0x65, 0x56, 0x61, 0x6c, 0x75, 0x65, 0x12, 0x23, 0x0a, 0x0c, 0x73,
	0x74, 0x72, 0x69, 0x6e, 0x67, 0x5f, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x18, 0x07, 0x20, 0x01, 0x28,
	0x09, 0x48, 0x00, 0x52, 0x0b, 0x73, 0x74, 0x72, 0x69, 0x6e, 0x67, 0x56, 0x61, 0x6c, 0x75, 0x65,
	0x12, 0x5b, 0x0a, 0x12, 0x64, 0x69, 0x73, 0x74, 0x72, 0x69, 0x62, 0x75, 0x74, 0x69, 0x6f, 0x6e,
	0x5f, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x18, 0x08, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x2a, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63,
	0x65, 0x63, 0x6f, 0x6e, 0x74, 0x72, 0x6f, 0x6c, 0x2e, 0x76, 0x31, 0x2e, 0x44, 0x69, 0x73, 0x74,
	0x72, 0x69, 0x62, 0x75, 0x74, 0x69, 0x6f, 0x6e, 0x48, 0x00, 0x52, 0x11, 0x64, 0x69, 0x73, 0x74,
	0x72, 0x69, 0x62, 0x75, 0x74, 0x69, 0x6f, 0x6e, 0x56, 0x61, 0x6c, 0x75, 0x65, 0x1a, 0x39, 0x0a,
	0x0b, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x45, 0x6e, 0x74, 0x72, 0x79, 0x12, 0x10, 0x0a, 0x03,
	0x6b, 0x65, 0x79, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x03, 0x6b, 0x65, 0x79, 0x12, 0x14,
	0x0a, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x18, 0x02, 0x20, 0x01, 0x28, 0x09, 0x52, 0x05, 0x76,
	0x61, 0x6c, 0x75, 0x65, 0x3a, 0x02, 0x38, 0x01, 0x42, 0x07, 0x0a, 0x05, 0x76, 0x61, 0x6c, 0x75,
	0x65, 0x22, 0x81, 0x01, 0x0a, 0x0e, 0x4d, 0x65, 0x74, 0x72, 0x69, 0x63, 0x56, 0x61, 0x6c, 0x75,
	0x65, 0x53, 0x65, 0x74, 0x12, 0x1f, 0x0a, 0x0b, 0x6d, 0x65, 0x74, 0x72, 0x69, 0x63, 0x5f, 0x6e,
	0x61, 0x6d, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x0a, 0x6d, 0x65, 0x74, 0x72, 0x69,
	0x63, 0x4e, 0x61, 0x6d, 0x65, 0x12, 0x4e, 0x0a, 0x0d, 0x6d, 0x65, 0x74, 0x72, 0x69, 0x63, 0x5f,
	0x76, 0x61, 0x6c, 0x75, 0x65, 0x73, 0x18, 0x02, 0x20, 0x03, 0x28, 0x0b, 0x32, 0x29, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63,
	0x65, 0x63, 0x6f, 0x6e, 0x74, 0x72, 0x6f, 0x6c, 0x2e, 0x76, 0x31, 0x2e, 0x4d, 0x65, 0x74, 0x72,
	0x69, 0x63, 0x56, 0x61, 0x6c, 0x75, 0x65, 0x52, 0x0c, 0x6d, 0x65, 0x74, 0x72, 0x69, 0x63, 0x56,
	0x61, 0x6c, 0x75, 0x65, 0x73, 0x42, 0x88, 0x01, 0x0a, 0x20, 0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65,
	0x63, 0x6f, 0x6e, 0x74, 0x72, 0x6f, 0x6c, 0x2e, 0x76, 0x31, 0x42, 0x13, 0x4d, 0x65, 0x74, 0x72,
	0x69, 0x63, 0x56, 0x61, 0x6c, 0x75, 0x65, 0x53, 0x65, 0x74, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50,
	0x01, 0x5a, 0x4a, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67,
	0x2e, 0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x73, 0x65, 0x72,
	0x76, 0x69, 0x63, 0x65, 0x63, 0x6f, 0x6e, 0x74, 0x72, 0x6f, 0x6c, 0x2f, 0x76, 0x31, 0x3b, 0x73,
	0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x63, 0x6f, 0x6e, 0x74, 0x72, 0x6f, 0x6c, 0xf8, 0x01, 0x01,
	0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_api_servicecontrol_v1_metric_value_proto_rawDescOnce sync.Once
	file_google_api_servicecontrol_v1_metric_value_proto_rawDescData = file_google_api_servicecontrol_v1_metric_value_proto_rawDesc
)

func file_google_api_servicecontrol_v1_metric_value_proto_rawDescGZIP() []byte {
	file_google_api_servicecontrol_v1_metric_value_proto_rawDescOnce.Do(func() {
		file_google_api_servicecontrol_v1_metric_value_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_api_servicecontrol_v1_metric_value_proto_rawDescData)
	})
	return file_google_api_servicecontrol_v1_metric_value_proto_rawDescData
}

var file_google_api_servicecontrol_v1_metric_value_proto_msgTypes = make([]protoimpl.MessageInfo, 3)
var file_google_api_servicecontrol_v1_metric_value_proto_goTypes = []interface{}{
	(*MetricValue)(nil),         // 0: google.api.servicecontrol.v1.MetricValue
	(*MetricValueSet)(nil),      // 1: google.api.servicecontrol.v1.MetricValueSet
	nil,                         // 2: google.api.servicecontrol.v1.MetricValue.LabelsEntry
	(*timestamp.Timestamp)(nil), // 3: google.protobuf.Timestamp
	(*Distribution)(nil),        // 4: google.api.servicecontrol.v1.Distribution
}
var file_google_api_servicecontrol_v1_metric_value_proto_depIdxs = []int32{
	2, // 0: google.api.servicecontrol.v1.MetricValue.labels:type_name -> google.api.servicecontrol.v1.MetricValue.LabelsEntry
	3, // 1: google.api.servicecontrol.v1.MetricValue.start_time:type_name -> google.protobuf.Timestamp
	3, // 2: google.api.servicecontrol.v1.MetricValue.end_time:type_name -> google.protobuf.Timestamp
	4, // 3: google.api.servicecontrol.v1.MetricValue.distribution_value:type_name -> google.api.servicecontrol.v1.Distribution
	0, // 4: google.api.servicecontrol.v1.MetricValueSet.metric_values:type_name -> google.api.servicecontrol.v1.MetricValue
	5, // [5:5] is the sub-list for method output_type
	5, // [5:5] is the sub-list for method input_type
	5, // [5:5] is the sub-list for extension type_name
	5, // [5:5] is the sub-list for extension extendee
	0, // [0:5] is the sub-list for field type_name
}

func init() { file_google_api_servicecontrol_v1_metric_value_proto_init() }
func file_google_api_servicecontrol_v1_metric_value_proto_init() {
	if File_google_api_servicecontrol_v1_metric_value_proto != nil {
		return
	}
	file_google_api_servicecontrol_v1_distribution_proto_init()
	if !protoimpl.UnsafeEnabled {
		file_google_api_servicecontrol_v1_metric_value_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MetricValue); i {
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
		file_google_api_servicecontrol_v1_metric_value_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MetricValueSet); i {
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
	file_google_api_servicecontrol_v1_metric_value_proto_msgTypes[0].OneofWrappers = []interface{}{
		(*MetricValue_BoolValue)(nil),
		(*MetricValue_Int64Value)(nil),
		(*MetricValue_DoubleValue)(nil),
		(*MetricValue_StringValue)(nil),
		(*MetricValue_DistributionValue)(nil),
	}
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: file_google_api_servicecontrol_v1_metric_value_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   3,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_api_servicecontrol_v1_metric_value_proto_goTypes,
		DependencyIndexes: file_google_api_servicecontrol_v1_metric_value_proto_depIdxs,
		MessageInfos:      file_google_api_servicecontrol_v1_metric_value_proto_msgTypes,
	}.Build()
	File_google_api_servicecontrol_v1_metric_value_proto = out.File
	file_google_api_servicecontrol_v1_metric_value_proto_rawDesc = nil
	file_google_api_servicecontrol_v1_metric_value_proto_goTypes = nil
	file_google_api_servicecontrol_v1_metric_value_proto_depIdxs = nil
}
