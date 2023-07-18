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
// source: google/ads/googleads/v4/services/campaign_criterion_service.proto

package services

import (
	context "context"
	reflect "reflect"
	sync "sync"

	proto "github.com/golang/protobuf/proto"
	resources "google.golang.org/genproto/googleapis/ads/googleads/v4/resources"
	_ "google.golang.org/genproto/googleapis/api/annotations"
	status "google.golang.org/genproto/googleapis/rpc/status"
	field_mask "google.golang.org/genproto/protobuf/field_mask"
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

// Request message for [CampaignCriterionService.GetCampaignCriterion][google.ads.googleads.v4.services.CampaignCriterionService.GetCampaignCriterion].
type GetCampaignCriterionRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Required. The resource name of the criterion to fetch.
	ResourceName string `protobuf:"bytes,1,opt,name=resource_name,json=resourceName,proto3" json:"resource_name,omitempty"`
}

func (x *GetCampaignCriterionRequest) Reset() {
	*x = GetCampaignCriterionRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *GetCampaignCriterionRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*GetCampaignCriterionRequest) ProtoMessage() {}

func (x *GetCampaignCriterionRequest) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use GetCampaignCriterionRequest.ProtoReflect.Descriptor instead.
func (*GetCampaignCriterionRequest) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescGZIP(), []int{0}
}

func (x *GetCampaignCriterionRequest) GetResourceName() string {
	if x != nil {
		return x.ResourceName
	}
	return ""
}

// Request message for [CampaignCriterionService.MutateCampaignCriteria][google.ads.googleads.v4.services.CampaignCriterionService.MutateCampaignCriteria].
type MutateCampaignCriteriaRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Required. The ID of the customer whose criteria are being modified.
	CustomerId string `protobuf:"bytes,1,opt,name=customer_id,json=customerId,proto3" json:"customer_id,omitempty"`
	// Required. The list of operations to perform on individual criteria.
	Operations []*CampaignCriterionOperation `protobuf:"bytes,2,rep,name=operations,proto3" json:"operations,omitempty"`
	// If true, successful operations will be carried out and invalid
	// operations will return errors. If false, all operations will be carried
	// out in one transaction if and only if they are all valid.
	// Default is false.
	PartialFailure bool `protobuf:"varint,3,opt,name=partial_failure,json=partialFailure,proto3" json:"partial_failure,omitempty"`
	// If true, the request is validated but not executed. Only errors are
	// returned, not results.
	ValidateOnly bool `protobuf:"varint,4,opt,name=validate_only,json=validateOnly,proto3" json:"validate_only,omitempty"`
}

func (x *MutateCampaignCriteriaRequest) Reset() {
	*x = MutateCampaignCriteriaRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MutateCampaignCriteriaRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MutateCampaignCriteriaRequest) ProtoMessage() {}

func (x *MutateCampaignCriteriaRequest) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MutateCampaignCriteriaRequest.ProtoReflect.Descriptor instead.
func (*MutateCampaignCriteriaRequest) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescGZIP(), []int{1}
}

func (x *MutateCampaignCriteriaRequest) GetCustomerId() string {
	if x != nil {
		return x.CustomerId
	}
	return ""
}

func (x *MutateCampaignCriteriaRequest) GetOperations() []*CampaignCriterionOperation {
	if x != nil {
		return x.Operations
	}
	return nil
}

func (x *MutateCampaignCriteriaRequest) GetPartialFailure() bool {
	if x != nil {
		return x.PartialFailure
	}
	return false
}

func (x *MutateCampaignCriteriaRequest) GetValidateOnly() bool {
	if x != nil {
		return x.ValidateOnly
	}
	return false
}

// A single operation (create, update, remove) on a campaign criterion.
type CampaignCriterionOperation struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// FieldMask that determines which resource fields are modified in an update.
	UpdateMask *field_mask.FieldMask `protobuf:"bytes,4,opt,name=update_mask,json=updateMask,proto3" json:"update_mask,omitempty"`
	// The mutate operation.
	//
	// Types that are assignable to Operation:
	//	*CampaignCriterionOperation_Create
	//	*CampaignCriterionOperation_Update
	//	*CampaignCriterionOperation_Remove
	Operation isCampaignCriterionOperation_Operation `protobuf_oneof:"operation"`
}

func (x *CampaignCriterionOperation) Reset() {
	*x = CampaignCriterionOperation{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[2]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *CampaignCriterionOperation) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*CampaignCriterionOperation) ProtoMessage() {}

func (x *CampaignCriterionOperation) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[2]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use CampaignCriterionOperation.ProtoReflect.Descriptor instead.
func (*CampaignCriterionOperation) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescGZIP(), []int{2}
}

func (x *CampaignCriterionOperation) GetUpdateMask() *field_mask.FieldMask {
	if x != nil {
		return x.UpdateMask
	}
	return nil
}

func (m *CampaignCriterionOperation) GetOperation() isCampaignCriterionOperation_Operation {
	if m != nil {
		return m.Operation
	}
	return nil
}

func (x *CampaignCriterionOperation) GetCreate() *resources.CampaignCriterion {
	if x, ok := x.GetOperation().(*CampaignCriterionOperation_Create); ok {
		return x.Create
	}
	return nil
}

func (x *CampaignCriterionOperation) GetUpdate() *resources.CampaignCriterion {
	if x, ok := x.GetOperation().(*CampaignCriterionOperation_Update); ok {
		return x.Update
	}
	return nil
}

func (x *CampaignCriterionOperation) GetRemove() string {
	if x, ok := x.GetOperation().(*CampaignCriterionOperation_Remove); ok {
		return x.Remove
	}
	return ""
}

type isCampaignCriterionOperation_Operation interface {
	isCampaignCriterionOperation_Operation()
}

type CampaignCriterionOperation_Create struct {
	// Create operation: No resource name is expected for the new criterion.
	Create *resources.CampaignCriterion `protobuf:"bytes,1,opt,name=create,proto3,oneof"`
}

type CampaignCriterionOperation_Update struct {
	// Update operation: The criterion is expected to have a valid resource
	// name.
	Update *resources.CampaignCriterion `protobuf:"bytes,2,opt,name=update,proto3,oneof"`
}

type CampaignCriterionOperation_Remove struct {
	// Remove operation: A resource name for the removed criterion is expected,
	// in this format:
	//
	// `customers/{customer_id}/campaignCriteria/{campaign_id}~{criterion_id}`
	Remove string `protobuf:"bytes,3,opt,name=remove,proto3,oneof"`
}

func (*CampaignCriterionOperation_Create) isCampaignCriterionOperation_Operation() {}

func (*CampaignCriterionOperation_Update) isCampaignCriterionOperation_Operation() {}

func (*CampaignCriterionOperation_Remove) isCampaignCriterionOperation_Operation() {}

// Response message for campaign criterion mutate.
type MutateCampaignCriteriaResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Errors that pertain to operation failures in the partial failure mode.
	// Returned only when partial_failure = true and all errors occur inside the
	// operations. If any errors occur outside the operations (e.g. auth errors),
	// we return an RPC level error.
	PartialFailureError *status.Status `protobuf:"bytes,3,opt,name=partial_failure_error,json=partialFailureError,proto3" json:"partial_failure_error,omitempty"`
	// All results for the mutate.
	Results []*MutateCampaignCriterionResult `protobuf:"bytes,2,rep,name=results,proto3" json:"results,omitempty"`
}

func (x *MutateCampaignCriteriaResponse) Reset() {
	*x = MutateCampaignCriteriaResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[3]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MutateCampaignCriteriaResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MutateCampaignCriteriaResponse) ProtoMessage() {}

func (x *MutateCampaignCriteriaResponse) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[3]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MutateCampaignCriteriaResponse.ProtoReflect.Descriptor instead.
func (*MutateCampaignCriteriaResponse) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescGZIP(), []int{3}
}

func (x *MutateCampaignCriteriaResponse) GetPartialFailureError() *status.Status {
	if x != nil {
		return x.PartialFailureError
	}
	return nil
}

func (x *MutateCampaignCriteriaResponse) GetResults() []*MutateCampaignCriterionResult {
	if x != nil {
		return x.Results
	}
	return nil
}

// The result for the criterion mutate.
type MutateCampaignCriterionResult struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Returned for successful operations.
	ResourceName string `protobuf:"bytes,1,opt,name=resource_name,json=resourceName,proto3" json:"resource_name,omitempty"`
}

func (x *MutateCampaignCriterionResult) Reset() {
	*x = MutateCampaignCriterionResult{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[4]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *MutateCampaignCriterionResult) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*MutateCampaignCriterionResult) ProtoMessage() {}

func (x *MutateCampaignCriterionResult) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[4]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use MutateCampaignCriterionResult.ProtoReflect.Descriptor instead.
func (*MutateCampaignCriterionResult) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescGZIP(), []int{4}
}

func (x *MutateCampaignCriterionResult) GetResourceName() string {
	if x != nil {
		return x.ResourceName
	}
	return ""
}

var File_google_ads_googleads_v4_services_campaign_criterion_service_proto protoreflect.FileDescriptor

var file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDesc = []byte{
	0x0a, 0x41, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x34, 0x2f, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63,
	0x65, 0x73, 0x2f, 0x63, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x5f, 0x63, 0x72, 0x69, 0x74,
	0x65, 0x72, 0x69, 0x6f, 0x6e, 0x5f, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x2e, 0x70, 0x72,
	0x6f, 0x74, 0x6f, 0x12, 0x20, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x73, 0x65, 0x72,
	0x76, 0x69, 0x63, 0x65, 0x73, 0x1a, 0x3a, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x64,
	0x73, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x34, 0x2f, 0x72,
	0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x73, 0x2f, 0x63, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67,
	0x6e, 0x5f, 0x63, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x2e, 0x70, 0x72, 0x6f, 0x74,
	0x6f, 0x1a, 0x1c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x61, 0x6e,
	0x6e, 0x6f, 0x74, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a,
	0x17, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x63, 0x6c, 0x69, 0x65,
	0x6e, 0x74, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x1f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x2f, 0x61, 0x70, 0x69, 0x2f, 0x66, 0x69, 0x65, 0x6c, 0x64, 0x5f, 0x62, 0x65, 0x68, 0x61, 0x76,
	0x69, 0x6f, 0x72, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x19, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x2e, 0x70,
	0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x20, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x70, 0x72, 0x6f,
	0x74, 0x6f, 0x62, 0x75, 0x66, 0x2f, 0x66, 0x69, 0x65, 0x6c, 0x64, 0x5f, 0x6d, 0x61, 0x73, 0x6b,
	0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x17, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x72,
	0x70, 0x63, 0x2f, 0x73, 0x74, 0x61, 0x74, 0x75, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22,
	0x76, 0x0a, 0x1b, 0x47, 0x65, 0x74, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43, 0x72,
	0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x12, 0x57,
	0x0a, 0x0d, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x5f, 0x6e, 0x61, 0x6d, 0x65, 0x18,
	0x01, 0x20, 0x01, 0x28, 0x09, 0x42, 0x32, 0xe0, 0x41, 0x02, 0xfa, 0x41, 0x2c, 0x0a, 0x2a, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61,
	0x70, 0x69, 0x73, 0x2e, 0x63, 0x6f, 0x6d, 0x2f, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e,
	0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x52, 0x0c, 0x72, 0x65, 0x73, 0x6f, 0x75,
	0x72, 0x63, 0x65, 0x4e, 0x61, 0x6d, 0x65, 0x22, 0xf6, 0x01, 0x0a, 0x1d, 0x4d, 0x75, 0x74, 0x61,
	0x74, 0x65, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72,
	0x69, 0x61, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x12, 0x24, 0x0a, 0x0b, 0x63, 0x75, 0x73,
	0x74, 0x6f, 0x6d, 0x65, 0x72, 0x5f, 0x69, 0x64, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x42, 0x03,
	0xe0, 0x41, 0x02, 0x52, 0x0a, 0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x65, 0x72, 0x49, 0x64, 0x12,
	0x61, 0x0a, 0x0a, 0x6f, 0x70, 0x65, 0x72, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x18, 0x02, 0x20,
	0x03, 0x28, 0x0b, 0x32, 0x3c, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73,
	0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x73, 0x65,
	0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0x2e, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43,
	0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x4f, 0x70, 0x65, 0x72, 0x61, 0x74, 0x69, 0x6f,
	0x6e, 0x42, 0x03, 0xe0, 0x41, 0x02, 0x52, 0x0a, 0x6f, 0x70, 0x65, 0x72, 0x61, 0x74, 0x69, 0x6f,
	0x6e, 0x73, 0x12, 0x27, 0x0a, 0x0f, 0x70, 0x61, 0x72, 0x74, 0x69, 0x61, 0x6c, 0x5f, 0x66, 0x61,
	0x69, 0x6c, 0x75, 0x72, 0x65, 0x18, 0x03, 0x20, 0x01, 0x28, 0x08, 0x52, 0x0e, 0x70, 0x61, 0x72,
	0x74, 0x69, 0x61, 0x6c, 0x46, 0x61, 0x69, 0x6c, 0x75, 0x72, 0x65, 0x12, 0x23, 0x0a, 0x0d, 0x76,
	0x61, 0x6c, 0x69, 0x64, 0x61, 0x74, 0x65, 0x5f, 0x6f, 0x6e, 0x6c, 0x79, 0x18, 0x04, 0x20, 0x01,
	0x28, 0x08, 0x52, 0x0c, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x61, 0x74, 0x65, 0x4f, 0x6e, 0x6c, 0x79,
	0x22, 0xa0, 0x02, 0x0a, 0x1a, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69,
	0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x4f, 0x70, 0x65, 0x72, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x12,
	0x3b, 0x0a, 0x0b, 0x75, 0x70, 0x64, 0x61, 0x74, 0x65, 0x5f, 0x6d, 0x61, 0x73, 0x6b, 0x18, 0x04,
	0x20, 0x01, 0x28, 0x0b, 0x32, 0x1a, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x70, 0x72,
	0x6f, 0x74, 0x6f, 0x62, 0x75, 0x66, 0x2e, 0x46, 0x69, 0x65, 0x6c, 0x64, 0x4d, 0x61, 0x73, 0x6b,
	0x52, 0x0a, 0x75, 0x70, 0x64, 0x61, 0x74, 0x65, 0x4d, 0x61, 0x73, 0x6b, 0x12, 0x4e, 0x0a, 0x06,
	0x63, 0x72, 0x65, 0x61, 0x74, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x34, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x73,
	0x2e, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69,
	0x6f, 0x6e, 0x48, 0x00, 0x52, 0x06, 0x63, 0x72, 0x65, 0x61, 0x74, 0x65, 0x12, 0x4e, 0x0a, 0x06,
	0x75, 0x70, 0x64, 0x61, 0x74, 0x65, 0x18, 0x02, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x34, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x73,
	0x2e, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69,
	0x6f, 0x6e, 0x48, 0x00, 0x52, 0x06, 0x75, 0x70, 0x64, 0x61, 0x74, 0x65, 0x12, 0x18, 0x0a, 0x06,
	0x72, 0x65, 0x6d, 0x6f, 0x76, 0x65, 0x18, 0x03, 0x20, 0x01, 0x28, 0x09, 0x48, 0x00, 0x52, 0x06,
	0x72, 0x65, 0x6d, 0x6f, 0x76, 0x65, 0x42, 0x0b, 0x0a, 0x09, 0x6f, 0x70, 0x65, 0x72, 0x61, 0x74,
	0x69, 0x6f, 0x6e, 0x22, 0xc3, 0x01, 0x0a, 0x1e, 0x4d, 0x75, 0x74, 0x61, 0x74, 0x65, 0x43, 0x61,
	0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x61, 0x52, 0x65,
	0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x12, 0x46, 0x0a, 0x15, 0x70, 0x61, 0x72, 0x74, 0x69, 0x61,
	0x6c, 0x5f, 0x66, 0x61, 0x69, 0x6c, 0x75, 0x72, 0x65, 0x5f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x18,
	0x03, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x12, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x72,
	0x70, 0x63, 0x2e, 0x53, 0x74, 0x61, 0x74, 0x75, 0x73, 0x52, 0x13, 0x70, 0x61, 0x72, 0x74, 0x69,
	0x61, 0x6c, 0x46, 0x61, 0x69, 0x6c, 0x75, 0x72, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x12, 0x59,
	0x0a, 0x07, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73, 0x18, 0x02, 0x20, 0x03, 0x28, 0x0b, 0x32,
	0x3f, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63,
	0x65, 0x73, 0x2e, 0x4d, 0x75, 0x74, 0x61, 0x74, 0x65, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67,
	0x6e, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x52, 0x65, 0x73, 0x75, 0x6c, 0x74,
	0x52, 0x07, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73, 0x22, 0x44, 0x0a, 0x1d, 0x4d, 0x75, 0x74,
	0x61, 0x74, 0x65, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74, 0x65,
	0x72, 0x69, 0x6f, 0x6e, 0x52, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x12, 0x23, 0x0a, 0x0d, 0x72, 0x65,
	0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x5f, 0x6e, 0x61, 0x6d, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28,
	0x09, 0x52, 0x0c, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x4e, 0x61, 0x6d, 0x65, 0x32,
	0x8a, 0x04, 0x0a, 0x18, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74,
	0x65, 0x72, 0x69, 0x6f, 0x6e, 0x53, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x12, 0xd7, 0x01, 0x0a,
	0x14, 0x47, 0x65, 0x74, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74,
	0x65, 0x72, 0x69, 0x6f, 0x6e, 0x12, 0x3d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61,
	0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e,
	0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0x2e, 0x47, 0x65, 0x74, 0x43, 0x61, 0x6d, 0x70,
	0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x52, 0x65, 0x71,
	0x75, 0x65, 0x73, 0x74, 0x1a, 0x34, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64,
	0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x72,
	0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x73, 0x2e, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67,
	0x6e, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x22, 0x4a, 0x82, 0xd3, 0xe4, 0x93,
	0x02, 0x34, 0x12, 0x32, 0x2f, 0x76, 0x34, 0x2f, 0x7b, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63,
	0x65, 0x5f, 0x6e, 0x61, 0x6d, 0x65, 0x3d, 0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x65, 0x72, 0x73,
	0x2f, 0x2a, 0x2f, 0x63, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74, 0x65,
	0x72, 0x69, 0x61, 0x2f, 0x2a, 0x7d, 0xda, 0x41, 0x0d, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63,
	0x65, 0x5f, 0x6e, 0x61, 0x6d, 0x65, 0x12, 0xf6, 0x01, 0x0a, 0x16, 0x4d, 0x75, 0x74, 0x61, 0x74,
	0x65, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69,
	0x61, 0x12, 0x3f, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x73, 0x65, 0x72, 0x76,
	0x69, 0x63, 0x65, 0x73, 0x2e, 0x4d, 0x75, 0x74, 0x61, 0x74, 0x65, 0x43, 0x61, 0x6d, 0x70, 0x61,
	0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x61, 0x52, 0x65, 0x71, 0x75, 0x65,
	0x73, 0x74, 0x1a, 0x40, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x73, 0x65, 0x72,
	0x76, 0x69, 0x63, 0x65, 0x73, 0x2e, 0x4d, 0x75, 0x74, 0x61, 0x74, 0x65, 0x43, 0x61, 0x6d, 0x70,
	0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x61, 0x52, 0x65, 0x73, 0x70,
	0x6f, 0x6e, 0x73, 0x65, 0x22, 0x59, 0x82, 0xd3, 0xe4, 0x93, 0x02, 0x3a, 0x22, 0x35, 0x2f, 0x76,
	0x34, 0x2f, 0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x65, 0x72, 0x73, 0x2f, 0x7b, 0x63, 0x75, 0x73,
	0x74, 0x6f, 0x6d, 0x65, 0x72, 0x5f, 0x69, 0x64, 0x3d, 0x2a, 0x7d, 0x2f, 0x63, 0x61, 0x6d, 0x70,
	0x61, 0x69, 0x67, 0x6e, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x61, 0x3a, 0x6d, 0x75, 0x74,
	0x61, 0x74, 0x65, 0x3a, 0x01, 0x2a, 0xda, 0x41, 0x16, 0x63, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x65,
	0x72, 0x5f, 0x69, 0x64, 0x2c, 0x6f, 0x70, 0x65, 0x72, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x1a,
	0x1b, 0xca, 0x41, 0x18, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2e, 0x63, 0x6f, 0x6d, 0x42, 0x84, 0x02, 0x0a,
	0x24, 0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x73, 0x65, 0x72,
	0x76, 0x69, 0x63, 0x65, 0x73, 0x42, 0x1d, 0x43, 0x61, 0x6d, 0x70, 0x61, 0x69, 0x67, 0x6e, 0x43,
	0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e, 0x53, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x50,
	0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a, 0x48, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67,
	0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f,
	0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x61, 0x64,
	0x73, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x34, 0x2f, 0x73,
	0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0x3b, 0x73, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73,
	0xa2, 0x02, 0x03, 0x47, 0x41, 0x41, 0xaa, 0x02, 0x20, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e,
	0x41, 0x64, 0x73, 0x2e, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x2e, 0x56, 0x34,
	0x2e, 0x53, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0xca, 0x02, 0x20, 0x47, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x5c, 0x41, 0x64, 0x73, 0x5c, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73,
	0x5c, 0x56, 0x34, 0x5c, 0x53, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0xea, 0x02, 0x24, 0x47,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x3a, 0x3a, 0x41, 0x64, 0x73, 0x3a, 0x3a, 0x47, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x41, 0x64, 0x73, 0x3a, 0x3a, 0x56, 0x34, 0x3a, 0x3a, 0x53, 0x65, 0x72, 0x76, 0x69,
	0x63, 0x65, 0x73, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescOnce sync.Once
	file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescData = file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDesc
)

func file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescGZIP() []byte {
	file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescOnce.Do(func() {
		file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescData)
	})
	return file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDescData
}

var file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes = make([]protoimpl.MessageInfo, 5)
var file_google_ads_googleads_v4_services_campaign_criterion_service_proto_goTypes = []interface{}{
	(*GetCampaignCriterionRequest)(nil),    // 0: google.ads.googleads.v4.services.GetCampaignCriterionRequest
	(*MutateCampaignCriteriaRequest)(nil),  // 1: google.ads.googleads.v4.services.MutateCampaignCriteriaRequest
	(*CampaignCriterionOperation)(nil),     // 2: google.ads.googleads.v4.services.CampaignCriterionOperation
	(*MutateCampaignCriteriaResponse)(nil), // 3: google.ads.googleads.v4.services.MutateCampaignCriteriaResponse
	(*MutateCampaignCriterionResult)(nil),  // 4: google.ads.googleads.v4.services.MutateCampaignCriterionResult
	(*field_mask.FieldMask)(nil),           // 5: google.protobuf.FieldMask
	(*resources.CampaignCriterion)(nil),    // 6: google.ads.googleads.v4.resources.CampaignCriterion
	(*status.Status)(nil),                  // 7: google.rpc.Status
}
var file_google_ads_googleads_v4_services_campaign_criterion_service_proto_depIdxs = []int32{
	2, // 0: google.ads.googleads.v4.services.MutateCampaignCriteriaRequest.operations:type_name -> google.ads.googleads.v4.services.CampaignCriterionOperation
	5, // 1: google.ads.googleads.v4.services.CampaignCriterionOperation.update_mask:type_name -> google.protobuf.FieldMask
	6, // 2: google.ads.googleads.v4.services.CampaignCriterionOperation.create:type_name -> google.ads.googleads.v4.resources.CampaignCriterion
	6, // 3: google.ads.googleads.v4.services.CampaignCriterionOperation.update:type_name -> google.ads.googleads.v4.resources.CampaignCriterion
	7, // 4: google.ads.googleads.v4.services.MutateCampaignCriteriaResponse.partial_failure_error:type_name -> google.rpc.Status
	4, // 5: google.ads.googleads.v4.services.MutateCampaignCriteriaResponse.results:type_name -> google.ads.googleads.v4.services.MutateCampaignCriterionResult
	0, // 6: google.ads.googleads.v4.services.CampaignCriterionService.GetCampaignCriterion:input_type -> google.ads.googleads.v4.services.GetCampaignCriterionRequest
	1, // 7: google.ads.googleads.v4.services.CampaignCriterionService.MutateCampaignCriteria:input_type -> google.ads.googleads.v4.services.MutateCampaignCriteriaRequest
	6, // 8: google.ads.googleads.v4.services.CampaignCriterionService.GetCampaignCriterion:output_type -> google.ads.googleads.v4.resources.CampaignCriterion
	3, // 9: google.ads.googleads.v4.services.CampaignCriterionService.MutateCampaignCriteria:output_type -> google.ads.googleads.v4.services.MutateCampaignCriteriaResponse
	8, // [8:10] is the sub-list for method output_type
	6, // [6:8] is the sub-list for method input_type
	6, // [6:6] is the sub-list for extension type_name
	6, // [6:6] is the sub-list for extension extendee
	0, // [0:6] is the sub-list for field type_name
}

func init() { file_google_ads_googleads_v4_services_campaign_criterion_service_proto_init() }
func file_google_ads_googleads_v4_services_campaign_criterion_service_proto_init() {
	if File_google_ads_googleads_v4_services_campaign_criterion_service_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*GetCampaignCriterionRequest); i {
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
		file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MutateCampaignCriteriaRequest); i {
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
		file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[2].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*CampaignCriterionOperation); i {
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
		file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[3].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MutateCampaignCriteriaResponse); i {
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
		file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[4].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*MutateCampaignCriterionResult); i {
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
	file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes[2].OneofWrappers = []interface{}{
		(*CampaignCriterionOperation_Create)(nil),
		(*CampaignCriterionOperation_Update)(nil),
		(*CampaignCriterionOperation_Remove)(nil),
	}
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   5,
			NumExtensions: 0,
			NumServices:   1,
		},
		GoTypes:           file_google_ads_googleads_v4_services_campaign_criterion_service_proto_goTypes,
		DependencyIndexes: file_google_ads_googleads_v4_services_campaign_criterion_service_proto_depIdxs,
		MessageInfos:      file_google_ads_googleads_v4_services_campaign_criterion_service_proto_msgTypes,
	}.Build()
	File_google_ads_googleads_v4_services_campaign_criterion_service_proto = out.File
	file_google_ads_googleads_v4_services_campaign_criterion_service_proto_rawDesc = nil
	file_google_ads_googleads_v4_services_campaign_criterion_service_proto_goTypes = nil
	file_google_ads_googleads_v4_services_campaign_criterion_service_proto_depIdxs = nil
}

// Reference imports to suppress errors if they are not otherwise used.
var _ context.Context
var _ grpc.ClientConnInterface

// This is a compile-time assertion to ensure that this generated file
// is compatible with the grpc package it is being compiled against.
const _ = grpc.SupportPackageIsVersion6

// CampaignCriterionServiceClient is the client API for CampaignCriterionService service.
//
// For semantics around ctx use and closing/ending streaming RPCs, please refer to https://godoc.org/google.golang.org/grpc#ClientConn.NewStream.
type CampaignCriterionServiceClient interface {
	// Returns the requested criterion in full detail.
	GetCampaignCriterion(ctx context.Context, in *GetCampaignCriterionRequest, opts ...grpc.CallOption) (*resources.CampaignCriterion, error)
	// Creates, updates, or removes criteria. Operation statuses are returned.
	MutateCampaignCriteria(ctx context.Context, in *MutateCampaignCriteriaRequest, opts ...grpc.CallOption) (*MutateCampaignCriteriaResponse, error)
}

type campaignCriterionServiceClient struct {
	cc grpc.ClientConnInterface
}

func NewCampaignCriterionServiceClient(cc grpc.ClientConnInterface) CampaignCriterionServiceClient {
	return &campaignCriterionServiceClient{cc}
}

func (c *campaignCriterionServiceClient) GetCampaignCriterion(ctx context.Context, in *GetCampaignCriterionRequest, opts ...grpc.CallOption) (*resources.CampaignCriterion, error) {
	out := new(resources.CampaignCriterion)
	err := c.cc.Invoke(ctx, "/google.ads.googleads.v4.services.CampaignCriterionService/GetCampaignCriterion", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (c *campaignCriterionServiceClient) MutateCampaignCriteria(ctx context.Context, in *MutateCampaignCriteriaRequest, opts ...grpc.CallOption) (*MutateCampaignCriteriaResponse, error) {
	out := new(MutateCampaignCriteriaResponse)
	err := c.cc.Invoke(ctx, "/google.ads.googleads.v4.services.CampaignCriterionService/MutateCampaignCriteria", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// CampaignCriterionServiceServer is the server API for CampaignCriterionService service.
type CampaignCriterionServiceServer interface {
	// Returns the requested criterion in full detail.
	GetCampaignCriterion(context.Context, *GetCampaignCriterionRequest) (*resources.CampaignCriterion, error)
	// Creates, updates, or removes criteria. Operation statuses are returned.
	MutateCampaignCriteria(context.Context, *MutateCampaignCriteriaRequest) (*MutateCampaignCriteriaResponse, error)
}

// UnimplementedCampaignCriterionServiceServer can be embedded to have forward compatible implementations.
type UnimplementedCampaignCriterionServiceServer struct {
}

func (*UnimplementedCampaignCriterionServiceServer) GetCampaignCriterion(context.Context, *GetCampaignCriterionRequest) (*resources.CampaignCriterion, error) {
	return nil, status1.Errorf(codes.Unimplemented, "method GetCampaignCriterion not implemented")
}
func (*UnimplementedCampaignCriterionServiceServer) MutateCampaignCriteria(context.Context, *MutateCampaignCriteriaRequest) (*MutateCampaignCriteriaResponse, error) {
	return nil, status1.Errorf(codes.Unimplemented, "method MutateCampaignCriteria not implemented")
}

func RegisterCampaignCriterionServiceServer(s *grpc.Server, srv CampaignCriterionServiceServer) {
	s.RegisterService(&_CampaignCriterionService_serviceDesc, srv)
}

func _CampaignCriterionService_GetCampaignCriterion_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(GetCampaignCriterionRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(CampaignCriterionServiceServer).GetCampaignCriterion(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/google.ads.googleads.v4.services.CampaignCriterionService/GetCampaignCriterion",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(CampaignCriterionServiceServer).GetCampaignCriterion(ctx, req.(*GetCampaignCriterionRequest))
	}
	return interceptor(ctx, in, info, handler)
}

func _CampaignCriterionService_MutateCampaignCriteria_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(MutateCampaignCriteriaRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(CampaignCriterionServiceServer).MutateCampaignCriteria(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/google.ads.googleads.v4.services.CampaignCriterionService/MutateCampaignCriteria",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(CampaignCriterionServiceServer).MutateCampaignCriteria(ctx, req.(*MutateCampaignCriteriaRequest))
	}
	return interceptor(ctx, in, info, handler)
}

var _CampaignCriterionService_serviceDesc = grpc.ServiceDesc{
	ServiceName: "google.ads.googleads.v4.services.CampaignCriterionService",
	HandlerType: (*CampaignCriterionServiceServer)(nil),
	Methods: []grpc.MethodDesc{
		{
			MethodName: "GetCampaignCriterion",
			Handler:    _CampaignCriterionService_GetCampaignCriterion_Handler,
		},
		{
			MethodName: "MutateCampaignCriteria",
			Handler:    _CampaignCriterionService_MutateCampaignCriteria_Handler,
		},
	},
	Streams:  []grpc.StreamDesc{},
	Metadata: "google/ads/googleads/v4/services/campaign_criterion_service.proto",
}
