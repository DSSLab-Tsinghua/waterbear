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
// source: google/ads/googleads/v1/services/ad_group_label_service.proto

package services

import (
	context "context"
	reflect "reflect"
	sync "sync"

	proto "github.com/golang/protobuf/proto"
	resources "google.golang.org/genproto/googleapis/ads/googleads/v1/resources"
	_ "google.golang.org/genproto/googleapis/api/annotations"
	status "google.golang.org/genproto/googleapis/rpc/status"
	grpc "google.golang.org/grpc"
	codes "google.golang.org/grpc/codes"
	status1 "google.golang.org/grpc/status"
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

// Request message for [AdGroupLabelService.GetAdGroupLabel][google.ads.googleads.v1.services.AdGroupLabelService.GetAdGroupLabel].
type GetAdGroupLabelRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Required. The resource name of the ad group label to fetch.
	ResourceName string `protobuf:"bytes,1,opt,name=resource_name,json=resourceName,proto3" json:"resource_name,omitempty"`
}

func (x *GetAdGroupLabelRequest) Reset() {
	*x = GetAdGroupLabelRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *GetAdGroupLabelRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*GetAdGroupLabelRequest) ProtoMessage() {}

func (x *GetAdGroupLabelRequest) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use GetAdGroupLabelRequest.ProtoReflect.Descriptor instead.
func (*GetAdGroupLabelRequest) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescGZIP(), []int{0}
}

func (x *GetAdGroupLabelRequest) GetResourceName() string {
	if x != nil {
		return x.ResourceName
	}
	return ""
}

// Request message for [AdGroupLabelService.MutateAdGroupLabels][google.ads.googleads.v1.services.AdGroupLabelService.MutateAdGroupLabels].
type MutateAdGroupLabelsRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Required. ID of the customer whose ad group labels are being modified.
	CustomerId string `protobuf:"bytes,1,opt,name=customer_id,json=customerId,proto3" json:"customer_id,omitempty"`
	// Required. The list of operations to perform on ad group labels.
	Operations []*AdGroupLabelOperation `protobuf:"bytes,2,rep,name=operations,proto3" json:"operations,omitempty"`
	// If true, successful operations will be carried out and invalid
	// operations will return errors. If false, all operations will be carried
	// out in one transaction if and only if they are all valid.
	// Default is false.
	PartialFailure bool `protobuf:"varint,3,opt,name=partial_failure,json=partialFailure,proto3" json:"partial_failure,omitempty"`
	// If true, the request is validated but not executed. Only errors are
	// returned, not results.
	ValidateOnly bool `protobuf:"varint,4,opt,name=validate_only,json=validateOnly,proto3" json:"validate_only,omitempty"`
}

func (x *MutateAdGroupLabelsRequest) Reset() {
	*x = MutateAdGroupLabelsRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MutateAdGroupLabelsRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MutateAdGroupLabelsRequest) ProtoMessage() {}

func (x *MutateAdGroupLabelsRequest) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MutateAdGroupLabelsRequest.ProtoReflect.Descriptor instead.
func (*MutateAdGroupLabelsRequest) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescGZIP(), []int{1}
}

func (x *MutateAdGroupLabelsRequest) GetCustomerId() string {
	if x != nil {
		return x.CustomerId
	}
	return ""
}

func (x *MutateAdGroupLabelsRequest) GetOperations() []*AdGroupLabelOperation {
	if x != nil {
		return x.Operations
	}
	return nil
}

func (x *MutateAdGroupLabelsRequest) GetPartialFailure() bool {
	if x != nil {
		return x.PartialFailure
	}
	return false
}

func (x *MutateAdGroupLabelsRequest) GetValidateOnly() bool {
	if x != nil {
		return x.ValidateOnly
	}
	return false
}

// A single operation (create, remove) on an ad group label.
type AdGroupLabelOperation struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// The mutate operation.
	//
	// Types that are assignable to Operation:
	//	*AdGroupLabelOperation_Create
	//	*AdGroupLabelOperation_Remove
	Operation isAdGroupLabelOperation_Operation `protobuf_oneof:"operation"`
}

func (x *AdGroupLabelOperation) Reset() {
	*x = AdGroupLabelOperation{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[2]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *AdGroupLabelOperation) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*AdGroupLabelOperation) ProtoMessage() {}

func (x *AdGroupLabelOperation) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[2]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use AdGroupLabelOperation.ProtoReflect.Descriptor instead.
func (*AdGroupLabelOperation) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescGZIP(), []int{2}
}

func (m *AdGroupLabelOperation) GetOperation() isAdGroupLabelOperation_Operation {
	if m != nil {
		return m.Operation
	}
	return nil
}

func (x *AdGroupLabelOperation) GetCreate() *resources.AdGroupLabel {
	if x, ok := x.GetOperation().(*AdGroupLabelOperation_Create); ok {
		return x.Create
	}
	return nil
}

func (x *AdGroupLabelOperation) GetRemove() string {
	if x, ok := x.GetOperation().(*AdGroupLabelOperation_Remove); ok {
		return x.Remove
	}
	return ""
}

type isAdGroupLabelOperation_Operation interface {
	isAdGroupLabelOperation_Operation()
}

type AdGroupLabelOperation_Create struct {
	// Create operation: No resource name is expected for the new ad group
	// label.
	Create *resources.AdGroupLabel `protobuf:"bytes,1,opt,name=create,proto3,oneof"`
}

type AdGroupLabelOperation_Remove struct {
	// Remove operation: A resource name for the ad group label
	// being removed, in this format:
	//
	// `customers/{customer_id}/adGroupLabels/{ad_group_id}~{label_id}`
	Remove string `protobuf:"bytes,2,opt,name=remove,proto3,oneof"`
}

func (*AdGroupLabelOperation_Create) isAdGroupLabelOperation_Operation() {}

func (*AdGroupLabelOperation_Remove) isAdGroupLabelOperation_Operation() {}

// Response message for an ad group labels mutate.
type MutateAdGroupLabelsResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Errors that pertain to operation failures in the partial failure mode.
	// Returned only when partial_failure = true and all errors occur inside the
	// operations. If any errors occur outside the operations (e.g. auth errors),
	// we return an RPC level error.
	PartialFailureError *status.Status `protobuf:"bytes,3,opt,name=partial_failure_error,json=partialFailureError,proto3" json:"partial_failure_error,omitempty"`
	// All results for the mutate.
	Results []*MutateAdGroupLabelResult `protobuf:"bytes,2,rep,name=results,proto3" json:"results,omitempty"`
}

func (x *MutateAdGroupLabelsResponse) Reset() {
	*x = MutateAdGroupLabelsResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[3]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MutateAdGroupLabelsResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MutateAdGroupLabelsResponse) ProtoMessage() {}

func (x *MutateAdGroupLabelsResponse) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[3]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MutateAdGroupLabelsResponse.ProtoReflect.Descriptor instead.
func (*MutateAdGroupLabelsResponse) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescGZIP(), []int{3}
}

func (x *MutateAdGroupLabelsResponse) GetPartialFailureError() *status.Status {
	if x != nil {
		return x.PartialFailureError
	}
	return nil
}

func (x *MutateAdGroupLabelsResponse) GetResults() []*MutateAdGroupLabelResult {
	if x != nil {
		return x.Results
	}
	return nil
}

// The result for an ad group label mutate.
type MutateAdGroupLabelResult struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Returned for successful operations.
	ResourceName string `protobuf:"bytes,1,opt,name=resource_name,json=resourceName,proto3" json:"resource_name,omitempty"`
}

func (x *MutateAdGroupLabelResult) Reset() {
	*x = MutateAdGroupLabelResult{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[4]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MutateAdGroupLabelResult) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MutateAdGroupLabelResult) ProtoMessage() {}

func (x *MutateAdGroupLabelResult) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[4]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MutateAdGroupLabelResult.ProtoReflect.Descriptor instead.
func (*MutateAdGroupLabelResult) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescGZIP(), []int{4}
}

func (x *MutateAdGroupLabelResult) GetResourceName() string {
	if x != nil {
		return x.ResourceName
	}
	return ""
}

var File_google_ads_googleads_v1_services_ad_group_label_service_proto protoreflect.FileDescriptor

var file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDesc = []byte{
	0x0a, 0x3d, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x31, 0x2f, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63,
	0x65, 0x73, 0x2f, 0x61, 0x64, 0x5f, 0x67, 0x72, 0x6f, 0x75, 0x70, 0x5f, 0x6c, 0x61, 0x62, 0x65,
	0x6c, 0x5f, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12,
	0x20, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x31, 0x2e, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65,
	0x73, 0x1a, 0x36, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x31, 0x2f, 0x72, 0x65, 0x73, 0x6f, 0x75,
	0x72, 0x63, 0x65, 0x73, 0x2f, 0x61, 0x64, 0x5f, 0x67, 0x72, 0x6f, 0x75, 0x70, 0x5f, 0x6c, 0x61,
	0x62, 0x65, 0x6c, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x1c, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x61, 0x6e, 0x6e, 0x6f, 0x74, 0x61, 0x74, 0x69, 0x6f, 0x6e,
	0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x17, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f,
	0x61, 0x70, 0x69, 0x2f, 0x63, 0x6c, 0x69, 0x65, 0x6e, 0x74, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f,
	0x1a, 0x1f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x66, 0x69, 0x65,
	0x6c, 0x64, 0x5f, 0x62, 0x65, 0x68, 0x61, 0x76, 0x69, 0x6f, 0x72, 0x2e, 0x70, 0x72, 0x6f, 0x74,
	0x6f, 0x1a, 0x19, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x72, 0x65,
	0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x17, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x72, 0x70, 0x63, 0x2f, 0x73, 0x74, 0x61, 0x74, 0x75, 0x73, 0x2e,
	0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22, 0x6c, 0x0a, 0x16, 0x47, 0x65, 0x74, 0x41, 0x64, 0x47, 0x72,
	0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x12,
	0x52, 0x0a, 0x0d, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x5f, 0x6e, 0x61, 0x6d, 0x65,
	0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x42, 0x2d, 0xe0, 0x41, 0x02, 0xfa, 0x41, 0x27, 0x0a, 0x25,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x61, 0x70, 0x69, 0x73, 0x2e, 0x63, 0x6f, 0x6d, 0x2f, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70,
	0x4c, 0x61, 0x62, 0x65, 0x6c, 0x52, 0x0c, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x4e,
	0x61, 0x6d, 0x65, 0x22, 0xee, 0x01, 0x0a, 0x1a, 0x4d, 0x75, 0x74, 0x61, 0x74, 0x65, 0x41, 0x64,
	0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x52, 0x65, 0x71, 0x75, 0x65,
	0x73, 0x74, 0x12, 0x24, 0x0a, 0x0b, 0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x65, 0x72, 0x5f, 0x69,
	0x64, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x42, 0x03, 0xe0, 0x41, 0x02, 0x52, 0x0a, 0x63, 0x75,
	0x73, 0x74, 0x6f, 0x6d, 0x65, 0x72, 0x49, 0x64, 0x12, 0x5c, 0x0a, 0x0a, 0x6f, 0x70, 0x65, 0x72,
	0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x18, 0x02, 0x20, 0x03, 0x28, 0x0b, 0x32, 0x37, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x61, 0x64, 0x73, 0x2e, 0x76, 0x31, 0x2e, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0x2e,
	0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x4f, 0x70, 0x65, 0x72,
	0x61, 0x74, 0x69, 0x6f, 0x6e, 0x42, 0x03, 0xe0, 0x41, 0x02, 0x52, 0x0a, 0x6f, 0x70, 0x65, 0x72,
	0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x12, 0x27, 0x0a, 0x0f, 0x70, 0x61, 0x72, 0x74, 0x69, 0x61,
	0x6c, 0x5f, 0x66, 0x61, 0x69, 0x6c, 0x75, 0x72, 0x65, 0x18, 0x03, 0x20, 0x01, 0x28, 0x08, 0x52,
	0x0e, 0x70, 0x61, 0x72, 0x74, 0x69, 0x61, 0x6c, 0x46, 0x61, 0x69, 0x6c, 0x75, 0x72, 0x65, 0x12,
	0x23, 0x0a, 0x0d, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x61, 0x74, 0x65, 0x5f, 0x6f, 0x6e, 0x6c, 0x79,
	0x18, 0x04, 0x20, 0x01, 0x28, 0x08, 0x52, 0x0c, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x61, 0x74, 0x65,
	0x4f, 0x6e, 0x6c, 0x79, 0x22, 0x89, 0x01, 0x0a, 0x15, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70,
	0x4c, 0x61, 0x62, 0x65, 0x6c, 0x4f, 0x70, 0x65, 0x72, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x12, 0x49,
	0x0a, 0x06, 0x63, 0x72, 0x65, 0x61, 0x74, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x2f,
	0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x31, 0x2e, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63,
	0x65, 0x73, 0x2e, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x48,
	0x00, 0x52, 0x06, 0x63, 0x72, 0x65, 0x61, 0x74, 0x65, 0x12, 0x18, 0x0a, 0x06, 0x72, 0x65, 0x6d,
	0x6f, 0x76, 0x65, 0x18, 0x02, 0x20, 0x01, 0x28, 0x09, 0x48, 0x00, 0x52, 0x06, 0x72, 0x65, 0x6d,
	0x6f, 0x76, 0x65, 0x42, 0x0b, 0x0a, 0x09, 0x6f, 0x70, 0x65, 0x72, 0x61, 0x74, 0x69, 0x6f, 0x6e,
	0x22, 0xbb, 0x01, 0x0a, 0x1b, 0x4d, 0x75, 0x74, 0x61, 0x74, 0x65, 0x41, 0x64, 0x47, 0x72, 0x6f,
	0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65,
	0x12, 0x46, 0x0a, 0x15, 0x70, 0x61, 0x72, 0x74, 0x69, 0x61, 0x6c, 0x5f, 0x66, 0x61, 0x69, 0x6c,
	0x75, 0x72, 0x65, 0x5f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x18, 0x03, 0x20, 0x01, 0x28, 0x0b, 0x32,
	0x12, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x72, 0x70, 0x63, 0x2e, 0x53, 0x74, 0x61,
	0x74, 0x75, 0x73, 0x52, 0x13, 0x70, 0x61, 0x72, 0x74, 0x69, 0x61, 0x6c, 0x46, 0x61, 0x69, 0x6c,
	0x75, 0x72, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x12, 0x54, 0x0a, 0x07, 0x72, 0x65, 0x73, 0x75,
	0x6c, 0x74, 0x73, 0x18, 0x02, 0x20, 0x03, 0x28, 0x0b, 0x32, 0x3a, 0x2e, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73,
	0x2e, 0x76, 0x31, 0x2e, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0x2e, 0x4d, 0x75, 0x74,
	0x61, 0x74, 0x65, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x52,
	0x65, 0x73, 0x75, 0x6c, 0x74, 0x52, 0x07, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73, 0x22, 0x3f,
	0x0a, 0x18, 0x4d, 0x75, 0x74, 0x61, 0x74, 0x65, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c,
	0x61, 0x62, 0x65, 0x6c, 0x52, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x12, 0x23, 0x0a, 0x0d, 0x72, 0x65,
	0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x5f, 0x6e, 0x61, 0x6d, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28,
	0x09, 0x52, 0x0c, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x4e, 0x61, 0x6d, 0x65, 0x32,
	0xe7, 0x03, 0x0a, 0x13, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c,
	0x53, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x12, 0xc5, 0x01, 0x0a, 0x0f, 0x47, 0x65, 0x74, 0x41,
	0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x12, 0x38, 0x2e, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61,
	0x64, 0x73, 0x2e, 0x76, 0x31, 0x2e, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0x2e, 0x47,
	0x65, 0x74, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x52, 0x65,
	0x71, 0x75, 0x65, 0x73, 0x74, 0x1a, 0x2f, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61,
	0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x31, 0x2e,
	0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x73, 0x2e, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75,
	0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x22, 0x47, 0x82, 0xd3, 0xe4, 0x93, 0x02, 0x31, 0x12, 0x2f,
	0x2f, 0x76, 0x31, 0x2f, 0x7b, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x5f, 0x6e, 0x61,
	0x6d, 0x65, 0x3d, 0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x65, 0x72, 0x73, 0x2f, 0x2a, 0x2f, 0x61,
	0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x2f, 0x2a, 0x7d, 0xda,
	0x41, 0x0d, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x5f, 0x6e, 0x61, 0x6d, 0x65, 0x12,
	0xea, 0x01, 0x0a, 0x13, 0x4d, 0x75, 0x74, 0x61, 0x74, 0x65, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75,
	0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x12, 0x3c, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76,
	0x31, 0x2e, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0x2e, 0x4d, 0x75, 0x74, 0x61, 0x74,
	0x65, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x52, 0x65,
	0x71, 0x75, 0x65, 0x73, 0x74, 0x1a, 0x3d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61,
	0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x31, 0x2e,
	0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0x2e, 0x4d, 0x75, 0x74, 0x61, 0x74, 0x65, 0x41,
	0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x52, 0x65, 0x73, 0x70,
	0x6f, 0x6e, 0x73, 0x65, 0x22, 0x56, 0x82, 0xd3, 0xe4, 0x93, 0x02, 0x37, 0x22, 0x32, 0x2f, 0x76,
	0x31, 0x2f, 0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x65, 0x72, 0x73, 0x2f, 0x7b, 0x63, 0x75, 0x73,
	0x74, 0x6f, 0x6d, 0x65, 0x72, 0x5f, 0x69, 0x64, 0x3d, 0x2a, 0x7d, 0x2f, 0x61, 0x64, 0x47, 0x72,
	0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c, 0x73, 0x3a, 0x6d, 0x75, 0x74, 0x61, 0x74, 0x65,
	0x3a, 0x01, 0x2a, 0xda, 0x41, 0x16, 0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x65, 0x72, 0x5f, 0x69,
	0x64, 0x2c, 0x6f, 0x70, 0x65, 0x72, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x1a, 0x1b, 0xca, 0x41,
	0x18, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x61, 0x70, 0x69, 0x73, 0x2e, 0x63, 0x6f, 0x6d, 0x42, 0xff, 0x01, 0x0a, 0x24, 0x63, 0x6f,
	0x6d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x31, 0x2e, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63,
	0x65, 0x73, 0x42, 0x18, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x4c, 0x61, 0x62, 0x65, 0x6c,
	0x53, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a, 0x48,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72,
	0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x61, 0x64, 0x73, 0x2f, 0x76, 0x31, 0x2f, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0x3b,
	0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0xa2, 0x02, 0x03, 0x47, 0x41, 0x41, 0xaa, 0x02,
	0x20, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x41, 0x64, 0x73, 0x2e, 0x47, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x41, 0x64, 0x73, 0x2e, 0x56, 0x31, 0x2e, 0x53, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65,
	0x73, 0xca, 0x02, 0x20, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x5c, 0x41, 0x64, 0x73, 0x5c, 0x47,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x5c, 0x56, 0x31, 0x5c, 0x53, 0x65, 0x72, 0x76,
	0x69, 0x63, 0x65, 0x73, 0xea, 0x02, 0x24, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x3a, 0x3a, 0x41,
	0x64, 0x73, 0x3a, 0x3a, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x3a, 0x3a, 0x56,
	0x31, 0x3a, 0x3a, 0x53, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0x62, 0x06, 0x70, 0x72, 0x6f,
	0x74, 0x6f, 0x33,
}

var (
	file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescOnce sync.Once
	file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescData = file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDesc
)

func file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescGZIP() []byte {
	file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescOnce.Do(func() {
		file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescData)
	})
	return file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDescData
}

var file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes = make([]protoimpl.MessageInfo, 5)
var file_google_ads_googleads_v1_services_ad_group_label_service_proto_goTypes = []interface{}{
	(*GetAdGroupLabelRequest)(nil),      // 0: google.ads.googleads.v1.services.GetAdGroupLabelRequest
	(*MutateAdGroupLabelsRequest)(nil),  // 1: google.ads.googleads.v1.services.MutateAdGroupLabelsRequest
	(*AdGroupLabelOperation)(nil),       // 2: google.ads.googleads.v1.services.AdGroupLabelOperation
	(*MutateAdGroupLabelsResponse)(nil), // 3: google.ads.googleads.v1.services.MutateAdGroupLabelsResponse
	(*MutateAdGroupLabelResult)(nil),    // 4: google.ads.googleads.v1.services.MutateAdGroupLabelResult
	(*resources.AdGroupLabel)(nil),      // 5: google.ads.googleads.v1.resources.AdGroupLabel
	(*status.Status)(nil),               // 6: google.rpc.Status
}
var file_google_ads_googleads_v1_services_ad_group_label_service_proto_depIdxs = []int32{
	2, // 0: google.ads.googleads.v1.services.MutateAdGroupLabelsRequest.operations:type_name -> google.ads.googleads.v1.services.AdGroupLabelOperation
	5, // 1: google.ads.googleads.v1.services.AdGroupLabelOperation.create:type_name -> google.ads.googleads.v1.resources.AdGroupLabel
	6, // 2: google.ads.googleads.v1.services.MutateAdGroupLabelsResponse.partial_failure_error:type_name -> google.rpc.Status
	4, // 3: google.ads.googleads.v1.services.MutateAdGroupLabelsResponse.results:type_name -> google.ads.googleads.v1.services.MutateAdGroupLabelResult
	0, // 4: google.ads.googleads.v1.services.AdGroupLabelService.GetAdGroupLabel:input_type -> google.ads.googleads.v1.services.GetAdGroupLabelRequest
	1, // 5: google.ads.googleads.v1.services.AdGroupLabelService.MutateAdGroupLabels:input_type -> google.ads.googleads.v1.services.MutateAdGroupLabelsRequest
	5, // 6: google.ads.googleads.v1.services.AdGroupLabelService.GetAdGroupLabel:output_type -> google.ads.googleads.v1.resources.AdGroupLabel
	3, // 7: google.ads.googleads.v1.services.AdGroupLabelService.MutateAdGroupLabels:output_type -> google.ads.googleads.v1.services.MutateAdGroupLabelsResponse
	6, // [6:8] is the sub-list for method output_type
	4, // [4:6] is the sub-list for method input_type
	4, // [4:4] is the sub-list for extension type_name
	4, // [4:4] is the sub-list for extension extendee
	0, // [0:4] is the sub-list for field type_name
}

func init() { file_google_ads_googleads_v1_services_ad_group_label_service_proto_init() }
func file_google_ads_googleads_v1_services_ad_group_label_service_proto_init() {
	if File_google_ads_googleads_v1_services_ad_group_label_service_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*GetAdGroupLabelRequest); i {
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
		file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MutateAdGroupLabelsRequest); i {
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
		file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[2].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*AdGroupLabelOperation); i {
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
		file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[3].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MutateAdGroupLabelsResponse); i {
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
		file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[4].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MutateAdGroupLabelResult); i {
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
	file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes[2].OneofWrappers = []interface{}{
		(*AdGroupLabelOperation_Create)(nil),
		(*AdGroupLabelOperation_Remove)(nil),
	}
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   5,
			NumExtensions: 0,
			NumServices:   1,
		},
		GoTypes:           file_google_ads_googleads_v1_services_ad_group_label_service_proto_goTypes,
		DependencyIndexes: file_google_ads_googleads_v1_services_ad_group_label_service_proto_depIdxs,
		MessageInfos:      file_google_ads_googleads_v1_services_ad_group_label_service_proto_msgTypes,
	}.Build()
	File_google_ads_googleads_v1_services_ad_group_label_service_proto = out.File
	file_google_ads_googleads_v1_services_ad_group_label_service_proto_rawDesc = nil
	file_google_ads_googleads_v1_services_ad_group_label_service_proto_goTypes = nil
	file_google_ads_googleads_v1_services_ad_group_label_service_proto_depIdxs = nil
}

// Reference imports to suppress errors if they are not otherwise used.
var _ context.Context
var _ grpc.ClientConnInterface

// This is a compile-time assertion to ensure that this generated file
// is compatible with the grpc package it is being compiled against.
const _ = grpc.SupportPackageIsVersion6

// AdGroupLabelServiceClient is the client API for AdGroupLabelService service.
//
// For semantics around ctx use and closing/ending streaming RPCs, please refer to https://godoc.org/google.golang.org/grpc#ClientConn.NewStream.
type AdGroupLabelServiceClient interface {
	// Returns the requested ad group label in full detail.
	GetAdGroupLabel(ctx context.Context, in *GetAdGroupLabelRequest, opts ...grpc.CallOption) (*resources.AdGroupLabel, error)
	// Creates and removes ad group labels.
	// Operation statuses are returned.
	MutateAdGroupLabels(ctx context.Context, in *MutateAdGroupLabelsRequest, opts ...grpc.CallOption) (*MutateAdGroupLabelsResponse, error)
}

type adGroupLabelServiceClient struct {
	cc grpc.ClientConnInterface
}

func NewAdGroupLabelServiceClient(cc grpc.ClientConnInterface) AdGroupLabelServiceClient {
	return &adGroupLabelServiceClient{cc}
}

func (c *adGroupLabelServiceClient) GetAdGroupLabel(ctx context.Context, in *GetAdGroupLabelRequest, opts ...grpc.CallOption) (*resources.AdGroupLabel, error) {
	out := new(resources.AdGroupLabel)
	err := c.cc.Invoke(ctx, "/google.ads.googleads.v1.services.AdGroupLabelService/GetAdGroupLabel", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *adGroupLabelServiceClient) MutateAdGroupLabels(ctx context.Context, in *MutateAdGroupLabelsRequest, opts ...grpc.CallOption) (*MutateAdGroupLabelsResponse, error) {
	out := new(MutateAdGroupLabelsResponse)
	err := c.cc.Invoke(ctx, "/google.ads.googleads.v1.services.AdGroupLabelService/MutateAdGroupLabels", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// AdGroupLabelServiceServer is the server API for AdGroupLabelService service.
type AdGroupLabelServiceServer interface {
	// Returns the requested ad group label in full detail.
	GetAdGroupLabel(context.Context, *GetAdGroupLabelRequest) (*resources.AdGroupLabel, error)
	// Creates and removes ad group labels.
	// Operation statuses are returned.
	MutateAdGroupLabels(context.Context, *MutateAdGroupLabelsRequest) (*MutateAdGroupLabelsResponse, error)
}

// UnimplementedAdGroupLabelServiceServer can be embedded to have forward compatible implementations.
type UnimplementedAdGroupLabelServiceServer struct {
}

func (*UnimplementedAdGroupLabelServiceServer) GetAdGroupLabel(context.Context, *GetAdGroupLabelRequest) (*resources.AdGroupLabel, error) {
	return nil, status1.Errorf(codes.Unimplemented, "method GetAdGroupLabel not implemented")
}
func (*UnimplementedAdGroupLabelServiceServer) MutateAdGroupLabels(context.Context, *MutateAdGroupLabelsRequest) (*MutateAdGroupLabelsResponse, error) {
	return nil, status1.Errorf(codes.Unimplemented, "method MutateAdGroupLabels not implemented")
}

func RegisterAdGroupLabelServiceServer(s *grpc.Server, srv AdGroupLabelServiceServer) {
	s.RegisterService(&_AdGroupLabelService_serviceDesc, srv)
}

func _AdGroupLabelService_GetAdGroupLabel_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(GetAdGroupLabelRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(AdGroupLabelServiceServer).GetAdGroupLabel(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/google.ads.googleads.v1.services.AdGroupLabelService/GetAdGroupLabel",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(AdGroupLabelServiceServer).GetAdGroupLabel(ctx, req.(*GetAdGroupLabelRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _AdGroupLabelService_MutateAdGroupLabels_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(MutateAdGroupLabelsRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(AdGroupLabelServiceServer).MutateAdGroupLabels(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/google.ads.googleads.v1.services.AdGroupLabelService/MutateAdGroupLabels",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(AdGroupLabelServiceServer).MutateAdGroupLabels(ctx, req.(*MutateAdGroupLabelsRequest))
	}
	return interceptor(ctx, in, info, handler)
}

var _AdGroupLabelService_serviceDesc = grpc.ServiceDesc{
	ServiceName: "google.ads.googleads.v1.services.AdGroupLabelService",
	HandlerType: (*AdGroupLabelServiceServer)(nil),
	Methods: []grpc.MethodDesc{
		{
			MethodName: "GetAdGroupLabel",
			Handler:    _AdGroupLabelService_GetAdGroupLabel_Handler,
		},
		{
			MethodName: "MutateAdGroupLabels",
			Handler:    _AdGroupLabelService_MutateAdGroupLabels_Handler,
		},
	},
	Streams:  []grpc.StreamDesc{},
	Metadata: "google/ads/googleads/v1/services/ad_group_label_service.proto",
}
