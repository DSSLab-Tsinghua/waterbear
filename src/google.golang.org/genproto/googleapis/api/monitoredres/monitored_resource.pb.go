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
// source: google/api/monitored_resource.proto

package monitoredres

import (
	reflect "reflect"
	sync "sync"

	proto "github.com/golang/protobuf/proto"
	_struct "github.com/golang/protobuf/ptypes/struct"
	api "google.golang.org/genproto/googleapis/api"
	label "google.golang.org/genproto/googleapis/api/label"
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

// An object that describes the schema of a [MonitoredResource][google.api.MonitoredResource] object using a
// type name and a set of labels.  For example, the monitored resource
// descriptor for Google Compute Engine VM instances has a type of
// `"gce_instance"` and specifies the use of the labels `"instance_id"` and
// `"zone"` to identify particular VM instances.
//
// Different services can support different monitored resource types.
//
// The following are specific rules to service defined monitored resources for
// Monitoring and Logging:
//
// * The `type`, `display_name`, `description`, `labels` and `launch_stage`
//   fields are all required.
// * The first label of the monitored resource descriptor must be
//   `resource_container`. There are legacy monitored resource descritptors
//   start with `project_id`.
// * It must include a `location` label.
// * Maximum of default 5 service defined monitored resource descriptors
//   is allowed per service.
// * Maximum of default 10 labels per monitored resource is allowed.
//
// The default maximum limit can be overridden. Please follow
// https://cloud.google.com/monitoring/quotas
//
type MonitoredResourceDescriptor struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Optional. The resource name of the monitored resource descriptor:
	// `"projects/{project_id}/monitoredResourceDescriptors/{type}"` where
	// {type} is the value of the `type` field in this object and
	// {project_id} is a project ID that provides API-specific context for
	// accessing the type.  APIs that do not use project information can use the
	// resource name format `"monitoredResourceDescriptors/{type}"`.
	Name string `protobuf:"bytes,5,opt,name=name,proto3" json:"name,omitempty"`
	// Required. The monitored resource type. For example, the type
	// `cloudsql_database` represents databases in Google Cloud SQL.
	//
	// All service defined monitored resource types must be prefixed with the
	// service name, in the format of `{service name}/{relative resource name}`.
	// The relative resource name must follow:
	//
	// * Only upper and lower-case letters and digits are allowed.
	// * It must start with upper case character and is recommended to use Upper
	//   Camel Case style.
	// * The maximum number of characters allowed for the relative_resource_name
	//   is 100.
	//
	// Note there are legacy service monitored resources not following this rule.
	Type string `protobuf:"bytes,1,opt,name=type,proto3" json:"type,omitempty"`
	// Optional. A concise name for the monitored resource type that might be
	// displayed in user interfaces. It should be a Title Cased Noun Phrase,
	// without any article or other determiners. For example,
	// `"Google Cloud SQL Database"`.
	DisplayName string `protobuf:"bytes,2,opt,name=display_name,json=displayName,proto3" json:"display_name,omitempty"`
	// Optional. A detailed description of the monitored resource type that might
	// be used in documentation.
	Description string `protobuf:"bytes,3,opt,name=description,proto3" json:"description,omitempty"`
	// Required. A set of labels used to describe instances of this monitored
	// resource type.
	// The label key name must follow:
	//
	// * Only upper and lower-case letters, digits and underscores (_) are
	//   allowed.
	// * Label name must start with a letter or digit.
	// * The maximum length of a label name is 100 characters.
	//
	// For example, an individual Google Cloud SQL database is
	// identified by values for the labels `database_id` and `location`.
	Labels []*label.LabelDescriptor `protobuf:"bytes,4,rep,name=labels,proto3" json:"labels,omitempty"`
	// Optional. The launch stage of the monitored resource definition.
	LaunchStage api.LaunchStage `protobuf:"varint,7,opt,name=launch_stage,json=launchStage,proto3,enum=google.api.LaunchStage" json:"launch_stage,omitempty"`
}

func (x *MonitoredResourceDescriptor) Reset() {
	*x = MonitoredResourceDescriptor{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_api_monitored_resource_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MonitoredResourceDescriptor) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MonitoredResourceDescriptor) ProtoMessage() {}

func (x *MonitoredResourceDescriptor) ProtoReflect() protoreflect.Message {
	mi := &file_google_api_monitored_resource_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MonitoredResourceDescriptor.ProtoReflect.Descriptor instead.
func (*MonitoredResourceDescriptor) Descriptor() ([]byte, []int) {
	return file_google_api_monitored_resource_proto_rawDescGZIP(), []int{0}
}

func (x *MonitoredResourceDescriptor) GetName() string {
	if x != nil {
		return x.Name
	}
	return ""
}

func (x *MonitoredResourceDescriptor) GetType() string {
	if x != nil {
		return x.Type
	}
	return ""
}

func (x *MonitoredResourceDescriptor) GetDisplayName() string {
	if x != nil {
		return x.DisplayName
	}
	return ""
}

func (x *MonitoredResourceDescriptor) GetDescription() string {
	if x != nil {
		return x.Description
	}
	return ""
}

func (x *MonitoredResourceDescriptor) GetLabels() []*label.LabelDescriptor {
	if x != nil {
		return x.Labels
	}
	return nil
}

func (x *MonitoredResourceDescriptor) GetLaunchStage() api.LaunchStage {
	if x != nil {
		return x.LaunchStage
	}
	return api.LaunchStage_LAUNCH_STAGE_UNSPECIFIED
}

// An object representing a resource that can be used for monitoring, logging,
// billing, or other purposes. Examples include virtual machine instances,
// databases, and storage devices such as disks. The `type` field identifies a
// [MonitoredResourceDescriptor][google.api.MonitoredResourceDescriptor] object that describes the resource's
// schema. Information in the `labels` field identifies the actual resource and
// its attributes according to the schema. For example, a particular Compute
// Engine VM instance could be represented by the following object, because the
// [MonitoredResourceDescriptor][google.api.MonitoredResourceDescriptor] for `"gce_instance"` has labels
// `"instance_id"` and `"zone"`:
//
//     { "type": "gce_instance",
//       "labels": { "instance_id": "12345678901234",
//                   "zone": "us-central1-a" }}
type MonitoredResource struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Required. The monitored resource type. This field must match
	// the `type` field of a [MonitoredResourceDescriptor][google.api.MonitoredResourceDescriptor] object. For
	// example, the type of a Compute Engine VM instance is `gce_instance`.
	Type string `protobuf:"bytes,1,opt,name=type,proto3" json:"type,omitempty"`
	// Required. Values for all of the labels listed in the associated monitored
	// resource descriptor. For example, Compute Engine VM instances use the
	// labels `"project_id"`, `"instance_id"`, and `"zone"`.
	Labels map[string]string `protobuf:"bytes,2,rep,name=labels,proto3" json:"labels,omitempty" protobuf_key:"bytes,1,opt,name=key,proto3" protobuf_val:"bytes,2,opt,name=value,proto3"`
}

func (x *MonitoredResource) Reset() {
	*x = MonitoredResource{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_api_monitored_resource_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MonitoredResource) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MonitoredResource) ProtoMessage() {}

func (x *MonitoredResource) ProtoReflect() protoreflect.Message {
	mi := &file_google_api_monitored_resource_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MonitoredResource.ProtoReflect.Descriptor instead.
func (*MonitoredResource) Descriptor() ([]byte, []int) {
	return file_google_api_monitored_resource_proto_rawDescGZIP(), []int{1}
}

func (x *MonitoredResource) GetType() string {
	if x != nil {
		return x.Type
	}
	return ""
}

func (x *MonitoredResource) GetLabels() map[string]string {
	if x != nil {
		return x.Labels
	}
	return nil
}

// Auxiliary metadata for a [MonitoredResource][google.api.MonitoredResource] object.
// [MonitoredResource][google.api.MonitoredResource] objects contain the minimum set of information to
// uniquely identify a monitored resource instance. There is some other useful
// auxiliary metadata. Monitoring and Logging use an ingestion
// pipeline to extract metadata for cloud resources of all types, and store
// the metadata in this message.
type MonitoredResourceMetadata struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Output only. Values for predefined system metadata labels.
	// System labels are a kind of metadata extracted by Google, including
	// "machine_image", "vpc", "subnet_id",
	// "security_group", "name", etc.
	// System label values can be only strings, Boolean values, or a list of
	// strings. For example:
	//
	//     { "name": "my-test-instance",
	//       "security_group": ["a", "b", "c"],
	//       "spot_instance": false }
	SystemLabels *_struct.Struct `protobuf:"bytes,1,opt,name=system_labels,json=systemLabels,proto3" json:"system_labels,omitempty"`
	// Output only. A map of user-defined metadata labels.
	UserLabels map[string]string `protobuf:"bytes,2,rep,name=user_labels,json=userLabels,proto3" json:"user_labels,omitempty" protobuf_key:"bytes,1,opt,name=key,proto3" protobuf_val:"bytes,2,opt,name=value,proto3"`
}

func (x *MonitoredResourceMetadata) Reset() {
	*x = MonitoredResourceMetadata{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_api_monitored_resource_proto_msgTypes[2]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MonitoredResourceMetadata) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MonitoredResourceMetadata) ProtoMessage() {}

func (x *MonitoredResourceMetadata) ProtoReflect() protoreflect.Message {
	mi := &file_google_api_monitored_resource_proto_msgTypes[2]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MonitoredResourceMetadata.ProtoReflect.Descriptor instead.
func (*MonitoredResourceMetadata) Descriptor() ([]byte, []int) {
	return file_google_api_monitored_resource_proto_rawDescGZIP(), []int{2}
}

func (x *MonitoredResourceMetadata) GetSystemLabels() *_struct.Struct {
	if x != nil {
		return x.SystemLabels
	}
	return nil
}

func (x *MonitoredResourceMetadata) GetUserLabels() map[string]string {
	if x != nil {
		return x.UserLabels
	}
	return nil
}

var File_google_api_monitored_resource_proto protoreflect.FileDescriptor

var file_google_api_monitored_resource_proto_rawDesc = []byte{
	0x0a, 0x23, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x6d, 0x6f, 0x6e,
	0x69, 0x74, 0x6f, 0x72, 0x65, 0x64, 0x5f, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x2e,
	0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x0a, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70,
	0x69, 0x1a, 0x16, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x6c, 0x61,
	0x62, 0x65, 0x6c, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x1d, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x6c, 0x61, 0x75, 0x6e, 0x63, 0x68, 0x5f, 0x73, 0x74, 0x61,
	0x67, 0x65, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x1c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x2f, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x62, 0x75, 0x66, 0x2f, 0x73, 0x74, 0x72, 0x75, 0x63, 0x74,
	0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22, 0xfb, 0x01, 0x0a, 0x1b, 0x4d, 0x6f, 0x6e, 0x69, 0x74,
	0x6f, 0x72, 0x65, 0x64, 0x52, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x44, 0x65, 0x73, 0x63,
	0x72, 0x69, 0x70, 0x74, 0x6f, 0x72, 0x12, 0x12, 0x0a, 0x04, 0x6e, 0x61, 0x6d, 0x65, 0x18, 0x05,
	0x20, 0x01, 0x28, 0x09, 0x52, 0x04, 0x6e, 0x61, 0x6d, 0x65, 0x12, 0x12, 0x0a, 0x04, 0x74, 0x79,
	0x70, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x04, 0x74, 0x79, 0x70, 0x65, 0x12, 0x21,
	0x0a, 0x0c, 0x64, 0x69, 0x73, 0x70, 0x6c, 0x61, 0x79, 0x5f, 0x6e, 0x61, 0x6d, 0x65, 0x18, 0x02,
	0x20, 0x01, 0x28, 0x09, 0x52, 0x0b, 0x64, 0x69, 0x73, 0x70, 0x6c, 0x61, 0x79, 0x4e, 0x61, 0x6d,
	0x65, 0x12, 0x20, 0x0a, 0x0b, 0x64, 0x65, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x69, 0x6f, 0x6e,
	0x18, 0x03, 0x20, 0x01, 0x28, 0x09, 0x52, 0x0b, 0x64, 0x65, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74,
	0x69, 0x6f, 0x6e, 0x12, 0x33, 0x0a, 0x06, 0x6c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x18, 0x04, 0x20,
	0x03, 0x28, 0x0b, 0x32, 0x1b, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69,
	0x2e, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x44, 0x65, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x6f, 0x72,
	0x52, 0x06, 0x6c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x12, 0x3a, 0x0a, 0x0c, 0x6c, 0x61, 0x75, 0x6e,
	0x63, 0x68, 0x5f, 0x73, 0x74, 0x61, 0x67, 0x65, 0x18, 0x07, 0x20, 0x01, 0x28, 0x0e, 0x32, 0x17,
	0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x4c, 0x61, 0x75, 0x6e,
	0x63, 0x68, 0x53, 0x74, 0x61, 0x67, 0x65, 0x52, 0x0b, 0x6c, 0x61, 0x75, 0x6e, 0x63, 0x68, 0x53,
	0x74, 0x61, 0x67, 0x65, 0x22, 0xa5, 0x01, 0x0a, 0x11, 0x4d, 0x6f, 0x6e, 0x69, 0x74, 0x6f, 0x72,
	0x65, 0x64, 0x52, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x12, 0x12, 0x0a, 0x04, 0x74, 0x79,
	0x70, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x04, 0x74, 0x79, 0x70, 0x65, 0x12, 0x41,
	0x0a, 0x06, 0x6c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x18, 0x02, 0x20, 0x03, 0x28, 0x0b, 0x32, 0x29,
	0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x4d, 0x6f, 0x6e, 0x69,
	0x74, 0x6f, 0x72, 0x65, 0x64, 0x52, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x2e, 0x4c, 0x61,
	0x62, 0x65, 0x6c, 0x73, 0x45, 0x6e, 0x74, 0x72, 0x79, 0x52, 0x06, 0x6c, 0x61, 0x62, 0x65, 0x6c,
	0x73, 0x1a, 0x39, 0x0a, 0x0b, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x45, 0x6e, 0x74, 0x72, 0x79,
	0x12, 0x10, 0x0a, 0x03, 0x6b, 0x65, 0x79, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x03, 0x6b,
	0x65, 0x79, 0x12, 0x14, 0x0a, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x18, 0x02, 0x20, 0x01, 0x28,
	0x09, 0x52, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x3a, 0x02, 0x38, 0x01, 0x22, 0xf0, 0x01, 0x0a,
	0x19, 0x4d, 0x6f, 0x6e, 0x69, 0x74, 0x6f, 0x72, 0x65, 0x64, 0x52, 0x65, 0x73, 0x6f, 0x75, 0x72,
	0x63, 0x65, 0x4d, 0x65, 0x74, 0x61, 0x64, 0x61, 0x74, 0x61, 0x12, 0x3c, 0x0a, 0x0d, 0x73, 0x79,
	0x73, 0x74, 0x65, 0x6d, 0x5f, 0x6c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x18, 0x01, 0x20, 0x01, 0x28,
	0x0b, 0x32, 0x17, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f,
	0x62, 0x75, 0x66, 0x2e, 0x53, 0x74, 0x72, 0x75, 0x63, 0x74, 0x52, 0x0c, 0x73, 0x79, 0x73, 0x74,
	0x65, 0x6d, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x12, 0x56, 0x0a, 0x0b, 0x75, 0x73, 0x65, 0x72,
	0x5f, 0x6c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x18, 0x02, 0x20, 0x03, 0x28, 0x0b, 0x32, 0x35, 0x2e,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70, 0x69, 0x2e, 0x4d, 0x6f, 0x6e, 0x69, 0x74,
	0x6f, 0x72, 0x65, 0x64, 0x52, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x4d, 0x65, 0x74, 0x61,
	0x64, 0x61, 0x74, 0x61, 0x2e, 0x55, 0x73, 0x65, 0x72, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x45,
	0x6e, 0x74, 0x72, 0x79, 0x52, 0x0a, 0x75, 0x73, 0x65, 0x72, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73,
	0x1a, 0x3d, 0x0a, 0x0f, 0x55, 0x73, 0x65, 0x72, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x45, 0x6e,
	0x74, 0x72, 0x79, 0x12, 0x10, 0x0a, 0x03, 0x6b, 0x65, 0x79, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09,
	0x52, 0x03, 0x6b, 0x65, 0x79, 0x12, 0x14, 0x0a, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x18, 0x02,
	0x20, 0x01, 0x28, 0x09, 0x52, 0x05, 0x76, 0x61, 0x6c, 0x75, 0x65, 0x3a, 0x02, 0x38, 0x01, 0x42,
	0x79, 0x0a, 0x0e, 0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x70,
	0x69, 0x42, 0x16, 0x4d, 0x6f, 0x6e, 0x69, 0x74, 0x6f, 0x72, 0x65, 0x64, 0x52, 0x65, 0x73, 0x6f,
	0x75, 0x72, 0x63, 0x65, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a, 0x43, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f, 0x67,
	0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70,
	0x69, 0x73, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x6d, 0x6f, 0x6e, 0x69, 0x74, 0x6f, 0x72, 0x65, 0x64,
	0x72, 0x65, 0x73, 0x3b, 0x6d, 0x6f, 0x6e, 0x69, 0x74, 0x6f, 0x72, 0x65, 0x64, 0x72, 0x65, 0x73,
	0xf8, 0x01, 0x01, 0xa2, 0x02, 0x04, 0x47, 0x41, 0x50, 0x49, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74,
	0x6f, 0x33,
}

var (
	file_google_api_monitored_resource_proto_rawDescOnce sync.Once
	file_google_api_monitored_resource_proto_rawDescData = file_google_api_monitored_resource_proto_rawDesc
)

func file_google_api_monitored_resource_proto_rawDescGZIP() []byte {
	file_google_api_monitored_resource_proto_rawDescOnce.Do(func() {
		file_google_api_monitored_resource_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_api_monitored_resource_proto_rawDescData)
	})
	return file_google_api_monitored_resource_proto_rawDescData
}

var file_google_api_monitored_resource_proto_msgTypes = make([]protoimpl.MessageInfo, 5)
var file_google_api_monitored_resource_proto_goTypes = []interface{}{
	(*MonitoredResourceDescriptor)(nil), // 0: google.api.MonitoredResourceDescriptor
	(*MonitoredResource)(nil),           // 1: google.api.MonitoredResource
	(*MonitoredResourceMetadata)(nil),   // 2: google.api.MonitoredResourceMetadata
	nil,                                 // 3: google.api.MonitoredResource.LabelsEntry
	nil,                                 // 4: google.api.MonitoredResourceMetadata.UserLabelsEntry
	(*label.LabelDescriptor)(nil),       // 5: google.api.LabelDescriptor
	(api.LaunchStage)(0),                // 6: google.api.LaunchStage
	(*_struct.Struct)(nil),              // 7: google.protobuf.Struct
}
var file_google_api_monitored_resource_proto_depIdxs = []int32{
	5, // 0: google.api.MonitoredResourceDescriptor.labels:type_name -> google.api.LabelDescriptor
	6, // 1: google.api.MonitoredResourceDescriptor.launch_stage:type_name -> google.api.LaunchStage
	3, // 2: google.api.MonitoredResource.labels:type_name -> google.api.MonitoredResource.LabelsEntry
	7, // 3: google.api.MonitoredResourceMetadata.system_labels:type_name -> google.protobuf.Struct
	4, // 4: google.api.MonitoredResourceMetadata.user_labels:type_name -> google.api.MonitoredResourceMetadata.UserLabelsEntry
	5, // [5:5] is the sub-list for method output_type
	5, // [5:5] is the sub-list for method input_type
	5, // [5:5] is the sub-list for extension type_name
	5, // [5:5] is the sub-list for extension extendee
	0, // [0:5] is the sub-list for field type_name
}

func init() { file_google_api_monitored_resource_proto_init() }
func file_google_api_monitored_resource_proto_init() {
	if File_google_api_monitored_resource_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_api_monitored_resource_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MonitoredResourceDescriptor); i {
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
		file_google_api_monitored_resource_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MonitoredResource); i {
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
		file_google_api_monitored_resource_proto_msgTypes[2].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MonitoredResourceMetadata); i {
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
			RawDescriptor: file_google_api_monitored_resource_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   5,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_api_monitored_resource_proto_goTypes,
		DependencyIndexes: file_google_api_monitored_resource_proto_depIdxs,
		MessageInfos:      file_google_api_monitored_resource_proto_msgTypes,
	}.Build()
	File_google_api_monitored_resource_proto = out.File
	file_google_api_monitored_resource_proto_rawDesc = nil
	file_google_api_monitored_resource_proto_goTypes = nil
	file_google_api_monitored_resource_proto_depIdxs = nil
}
