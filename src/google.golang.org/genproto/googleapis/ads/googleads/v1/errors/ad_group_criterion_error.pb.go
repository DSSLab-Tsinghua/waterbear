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
// source: google/ads/googleads/v1/errors/ad_group_criterion_error.proto

package errors

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

// Enum describing possible ad group criterion errors.
type AdGroupCriterionErrorEnum_AdGroupCriterionError int32

const (
	// Enum unspecified.
	AdGroupCriterionErrorEnum_UNSPECIFIED AdGroupCriterionErrorEnum_AdGroupCriterionError = 0
	// The received error code is not known in this version.
	AdGroupCriterionErrorEnum_UNKNOWN AdGroupCriterionErrorEnum_AdGroupCriterionError = 1
	// No link found between the AdGroupCriterion and the label.
	AdGroupCriterionErrorEnum_AD_GROUP_CRITERION_LABEL_DOES_NOT_EXIST AdGroupCriterionErrorEnum_AdGroupCriterionError = 2
	// The label has already been attached to the AdGroupCriterion.
	AdGroupCriterionErrorEnum_AD_GROUP_CRITERION_LABEL_ALREADY_EXISTS AdGroupCriterionErrorEnum_AdGroupCriterionError = 3
	// Negative AdGroupCriterion cannot have labels.
	AdGroupCriterionErrorEnum_CANNOT_ADD_LABEL_TO_NEGATIVE_CRITERION AdGroupCriterionErrorEnum_AdGroupCriterionError = 4
	// Too many operations for a single call.
	AdGroupCriterionErrorEnum_TOO_MANY_OPERATIONS AdGroupCriterionErrorEnum_AdGroupCriterionError = 5
	// Negative ad group criteria are not updateable.
	AdGroupCriterionErrorEnum_CANT_UPDATE_NEGATIVE AdGroupCriterionErrorEnum_AdGroupCriterionError = 6
	// Concrete type of criterion (keyword v.s. placement) is required for ADD
	// and SET operations.
	AdGroupCriterionErrorEnum_CONCRETE_TYPE_REQUIRED AdGroupCriterionErrorEnum_AdGroupCriterionError = 7
	// Bid is incompatible with ad group's bidding settings.
	AdGroupCriterionErrorEnum_BID_INCOMPATIBLE_WITH_ADGROUP AdGroupCriterionErrorEnum_AdGroupCriterionError = 8
	// Cannot target and exclude the same criterion at once.
	AdGroupCriterionErrorEnum_CANNOT_TARGET_AND_EXCLUDE AdGroupCriterionErrorEnum_AdGroupCriterionError = 9
	// The URL of a placement is invalid.
	AdGroupCriterionErrorEnum_ILLEGAL_URL AdGroupCriterionErrorEnum_AdGroupCriterionError = 10
	// Keyword text was invalid.
	AdGroupCriterionErrorEnum_INVALID_KEYWORD_TEXT AdGroupCriterionErrorEnum_AdGroupCriterionError = 11
	// Destination URL was invalid.
	AdGroupCriterionErrorEnum_INVALID_DESTINATION_URL AdGroupCriterionErrorEnum_AdGroupCriterionError = 12
	// The destination url must contain at least one tag (e.g. {lpurl})
	AdGroupCriterionErrorEnum_MISSING_DESTINATION_URL_TAG AdGroupCriterionErrorEnum_AdGroupCriterionError = 13
	// Keyword-level cpm bid is not supported
	AdGroupCriterionErrorEnum_KEYWORD_LEVEL_BID_NOT_SUPPORTED_FOR_MANUALCPM AdGroupCriterionErrorEnum_AdGroupCriterionError = 14
	// For example, cannot add a biddable ad group criterion that had been
	// removed.
	AdGroupCriterionErrorEnum_INVALID_USER_STATUS AdGroupCriterionErrorEnum_AdGroupCriterionError = 15
	// Criteria type cannot be targeted for the ad group. Either the account is
	// restricted to keywords only, the criteria type is incompatible with the
	// campaign's bidding strategy, or the criteria type can only be applied to
	// campaigns.
	AdGroupCriterionErrorEnum_CANNOT_ADD_CRITERIA_TYPE AdGroupCriterionErrorEnum_AdGroupCriterionError = 16
	// Criteria type cannot be excluded for the ad group. Refer to the
	// documentation for a specific criterion to check if it is excludable.
	AdGroupCriterionErrorEnum_CANNOT_EXCLUDE_CRITERIA_TYPE AdGroupCriterionErrorEnum_AdGroupCriterionError = 17
	// Partial failure is not supported for shopping campaign mutate operations.
	AdGroupCriterionErrorEnum_CAMPAIGN_TYPE_NOT_COMPATIBLE_WITH_PARTIAL_FAILURE AdGroupCriterionErrorEnum_AdGroupCriterionError = 27
	// Operations in the mutate request changes too many shopping ad groups.
	// Please split requests for multiple shopping ad groups across multiple
	// requests.
	AdGroupCriterionErrorEnum_OPERATIONS_FOR_TOO_MANY_SHOPPING_ADGROUPS AdGroupCriterionErrorEnum_AdGroupCriterionError = 28
	// Not allowed to modify url fields of an ad group criterion if there are
	// duplicate elements for that ad group criterion in the request.
	AdGroupCriterionErrorEnum_CANNOT_MODIFY_URL_FIELDS_WITH_DUPLICATE_ELEMENTS AdGroupCriterionErrorEnum_AdGroupCriterionError = 29
	// Cannot set url fields without also setting final urls.
	AdGroupCriterionErrorEnum_CANNOT_SET_WITHOUT_FINAL_URLS AdGroupCriterionErrorEnum_AdGroupCriterionError = 30
	// Cannot clear final urls if final mobile urls exist.
	AdGroupCriterionErrorEnum_CANNOT_CLEAR_FINAL_URLS_IF_FINAL_MOBILE_URLS_EXIST AdGroupCriterionErrorEnum_AdGroupCriterionError = 31
	// Cannot clear final urls if final app urls exist.
	AdGroupCriterionErrorEnum_CANNOT_CLEAR_FINAL_URLS_IF_FINAL_APP_URLS_EXIST AdGroupCriterionErrorEnum_AdGroupCriterionError = 32
	// Cannot clear final urls if tracking url template exists.
	AdGroupCriterionErrorEnum_CANNOT_CLEAR_FINAL_URLS_IF_TRACKING_URL_TEMPLATE_EXISTS AdGroupCriterionErrorEnum_AdGroupCriterionError = 33
	// Cannot clear final urls if url custom parameters exist.
	AdGroupCriterionErrorEnum_CANNOT_CLEAR_FINAL_URLS_IF_URL_CUSTOM_PARAMETERS_EXIST AdGroupCriterionErrorEnum_AdGroupCriterionError = 34
	// Cannot set both destination url and final urls.
	AdGroupCriterionErrorEnum_CANNOT_SET_BOTH_DESTINATION_URL_AND_FINAL_URLS AdGroupCriterionErrorEnum_AdGroupCriterionError = 35
	// Cannot set both destination url and tracking url template.
	AdGroupCriterionErrorEnum_CANNOT_SET_BOTH_DESTINATION_URL_AND_TRACKING_URL_TEMPLATE AdGroupCriterionErrorEnum_AdGroupCriterionError = 36
	// Final urls are not supported for this criterion type.
	AdGroupCriterionErrorEnum_FINAL_URLS_NOT_SUPPORTED_FOR_CRITERION_TYPE AdGroupCriterionErrorEnum_AdGroupCriterionError = 37
	// Final mobile urls are not supported for this criterion type.
	AdGroupCriterionErrorEnum_FINAL_MOBILE_URLS_NOT_SUPPORTED_FOR_CRITERION_TYPE AdGroupCriterionErrorEnum_AdGroupCriterionError = 38
	// Ad group is invalid due to the listing groups it contains.
	AdGroupCriterionErrorEnum_INVALID_LISTING_GROUP_HIERARCHY AdGroupCriterionErrorEnum_AdGroupCriterionError = 39
	// Listing group unit cannot have children.
	AdGroupCriterionErrorEnum_LISTING_GROUP_UNIT_CANNOT_HAVE_CHILDREN AdGroupCriterionErrorEnum_AdGroupCriterionError = 40
	// Subdivided listing groups must have an "others" case.
	AdGroupCriterionErrorEnum_LISTING_GROUP_SUBDIVISION_REQUIRES_OTHERS_CASE AdGroupCriterionErrorEnum_AdGroupCriterionError = 41
	// Dimension type of listing group must be the same as that of its siblings.
	AdGroupCriterionErrorEnum_LISTING_GROUP_REQUIRES_SAME_DIMENSION_TYPE_AS_SIBLINGS AdGroupCriterionErrorEnum_AdGroupCriterionError = 42
	// Listing group cannot be added to the ad group because it already exists.
	AdGroupCriterionErrorEnum_LISTING_GROUP_ALREADY_EXISTS AdGroupCriterionErrorEnum_AdGroupCriterionError = 43
	// Listing group referenced in the operation was not found in the ad group.
	AdGroupCriterionErrorEnum_LISTING_GROUP_DOES_NOT_EXIST AdGroupCriterionErrorEnum_AdGroupCriterionError = 44
	// Recursive removal failed because listing group subdivision is being
	// created or modified in this request.
	AdGroupCriterionErrorEnum_LISTING_GROUP_CANNOT_BE_REMOVED AdGroupCriterionErrorEnum_AdGroupCriterionError = 45
	// Listing group type is not allowed for specified ad group criterion type.
	AdGroupCriterionErrorEnum_INVALID_LISTING_GROUP_TYPE AdGroupCriterionErrorEnum_AdGroupCriterionError = 46
	// Listing group in an ADD operation specifies a non temporary criterion id.
	AdGroupCriterionErrorEnum_LISTING_GROUP_ADD_MAY_ONLY_USE_TEMP_ID AdGroupCriterionErrorEnum_AdGroupCriterionError = 47
)

// Enum value maps for AdGroupCriterionErrorEnum_AdGroupCriterionError.
var (
	AdGroupCriterionErrorEnum_AdGroupCriterionError_name = map[int32]string{
		0:  "UNSPECIFIED",
		1:  "UNKNOWN",
		2:  "AD_GROUP_CRITERION_LABEL_DOES_NOT_EXIST",
		3:  "AD_GROUP_CRITERION_LABEL_ALREADY_EXISTS",
		4:  "CANNOT_ADD_LABEL_TO_NEGATIVE_CRITERION",
		5:  "TOO_MANY_OPERATIONS",
		6:  "CANT_UPDATE_NEGATIVE",
		7:  "CONCRETE_TYPE_REQUIRED",
		8:  "BID_INCOMPATIBLE_WITH_ADGROUP",
		9:  "CANNOT_TARGET_AND_EXCLUDE",
		10: "ILLEGAL_URL",
		11: "INVALID_KEYWORD_TEXT",
		12: "INVALID_DESTINATION_URL",
		13: "MISSING_DESTINATION_URL_TAG",
		14: "KEYWORD_LEVEL_BID_NOT_SUPPORTED_FOR_MANUALCPM",
		15: "INVALID_USER_STATUS",
		16: "CANNOT_ADD_CRITERIA_TYPE",
		17: "CANNOT_EXCLUDE_CRITERIA_TYPE",
		27: "CAMPAIGN_TYPE_NOT_COMPATIBLE_WITH_PARTIAL_FAILURE",
		28: "OPERATIONS_FOR_TOO_MANY_SHOPPING_ADGROUPS",
		29: "CANNOT_MODIFY_URL_FIELDS_WITH_DUPLICATE_ELEMENTS",
		30: "CANNOT_SET_WITHOUT_FINAL_URLS",
		31: "CANNOT_CLEAR_FINAL_URLS_IF_FINAL_MOBILE_URLS_EXIST",
		32: "CANNOT_CLEAR_FINAL_URLS_IF_FINAL_APP_URLS_EXIST",
		33: "CANNOT_CLEAR_FINAL_URLS_IF_TRACKING_URL_TEMPLATE_EXISTS",
		34: "CANNOT_CLEAR_FINAL_URLS_IF_URL_CUSTOM_PARAMETERS_EXIST",
		35: "CANNOT_SET_BOTH_DESTINATION_URL_AND_FINAL_URLS",
		36: "CANNOT_SET_BOTH_DESTINATION_URL_AND_TRACKING_URL_TEMPLATE",
		37: "FINAL_URLS_NOT_SUPPORTED_FOR_CRITERION_TYPE",
		38: "FINAL_MOBILE_URLS_NOT_SUPPORTED_FOR_CRITERION_TYPE",
		39: "INVALID_LISTING_GROUP_HIERARCHY",
		40: "LISTING_GROUP_UNIT_CANNOT_HAVE_CHILDREN",
		41: "LISTING_GROUP_SUBDIVISION_REQUIRES_OTHERS_CASE",
		42: "LISTING_GROUP_REQUIRES_SAME_DIMENSION_TYPE_AS_SIBLINGS",
		43: "LISTING_GROUP_ALREADY_EXISTS",
		44: "LISTING_GROUP_DOES_NOT_EXIST",
		45: "LISTING_GROUP_CANNOT_BE_REMOVED",
		46: "INVALID_LISTING_GROUP_TYPE",
		47: "LISTING_GROUP_ADD_MAY_ONLY_USE_TEMP_ID",
	}
	AdGroupCriterionErrorEnum_AdGroupCriterionError_value = map[string]int32{
		"UNSPECIFIED": 0,
		"UNKNOWN":     1,
		"AD_GROUP_CRITERION_LABEL_DOES_NOT_EXIST":                   2,
		"AD_GROUP_CRITERION_LABEL_ALREADY_EXISTS":                   3,
		"CANNOT_ADD_LABEL_TO_NEGATIVE_CRITERION":                    4,
		"TOO_MANY_OPERATIONS":                                       5,
		"CANT_UPDATE_NEGATIVE":                                      6,
		"CONCRETE_TYPE_REQUIRED":                                    7,
		"BID_INCOMPATIBLE_WITH_ADGROUP":                             8,
		"CANNOT_TARGET_AND_EXCLUDE":                                 9,
		"ILLEGAL_URL":                                               10,
		"INVALID_KEYWORD_TEXT":                                      11,
		"INVALID_DESTINATION_URL":                                   12,
		"MISSING_DESTINATION_URL_TAG":                               13,
		"KEYWORD_LEVEL_BID_NOT_SUPPORTED_FOR_MANUALCPM":             14,
		"INVALID_USER_STATUS":                                       15,
		"CANNOT_ADD_CRITERIA_TYPE":                                  16,
		"CANNOT_EXCLUDE_CRITERIA_TYPE":                              17,
		"CAMPAIGN_TYPE_NOT_COMPATIBLE_WITH_PARTIAL_FAILURE":         27,
		"OPERATIONS_FOR_TOO_MANY_SHOPPING_ADGROUPS":                 28,
		"CANNOT_MODIFY_URL_FIELDS_WITH_DUPLICATE_ELEMENTS":          29,
		"CANNOT_SET_WITHOUT_FINAL_URLS":                             30,
		"CANNOT_CLEAR_FINAL_URLS_IF_FINAL_MOBILE_URLS_EXIST":        31,
		"CANNOT_CLEAR_FINAL_URLS_IF_FINAL_APP_URLS_EXIST":           32,
		"CANNOT_CLEAR_FINAL_URLS_IF_TRACKING_URL_TEMPLATE_EXISTS":   33,
		"CANNOT_CLEAR_FINAL_URLS_IF_URL_CUSTOM_PARAMETERS_EXIST":    34,
		"CANNOT_SET_BOTH_DESTINATION_URL_AND_FINAL_URLS":            35,
		"CANNOT_SET_BOTH_DESTINATION_URL_AND_TRACKING_URL_TEMPLATE": 36,
		"FINAL_URLS_NOT_SUPPORTED_FOR_CRITERION_TYPE":               37,
		"FINAL_MOBILE_URLS_NOT_SUPPORTED_FOR_CRITERION_TYPE":        38,
		"INVALID_LISTING_GROUP_HIERARCHY":                           39,
		"LISTING_GROUP_UNIT_CANNOT_HAVE_CHILDREN":                   40,
		"LISTING_GROUP_SUBDIVISION_REQUIRES_OTHERS_CASE":            41,
		"LISTING_GROUP_REQUIRES_SAME_DIMENSION_TYPE_AS_SIBLINGS":    42,
		"LISTING_GROUP_ALREADY_EXISTS":                              43,
		"LISTING_GROUP_DOES_NOT_EXIST":                              44,
		"LISTING_GROUP_CANNOT_BE_REMOVED":                           45,
		"INVALID_LISTING_GROUP_TYPE":                                46,
		"LISTING_GROUP_ADD_MAY_ONLY_USE_TEMP_ID":                    47,
	}
)

func (x AdGroupCriterionErrorEnum_AdGroupCriterionError) Enum() *AdGroupCriterionErrorEnum_AdGroupCriterionError {
	p := new(AdGroupCriterionErrorEnum_AdGroupCriterionError)
	*p = x
	return p
}

func (x AdGroupCriterionErrorEnum_AdGroupCriterionError) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (AdGroupCriterionErrorEnum_AdGroupCriterionError) Descriptor() protoreflect.EnumDescriptor {
	return file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_enumTypes[0].Descriptor()
}

func (AdGroupCriterionErrorEnum_AdGroupCriterionError) Type() protoreflect.EnumType {
	return &file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_enumTypes[0]
}

func (x AdGroupCriterionErrorEnum_AdGroupCriterionError) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use AdGroupCriterionErrorEnum_AdGroupCriterionError.Descriptor instead.
func (AdGroupCriterionErrorEnum_AdGroupCriterionError) EnumDescriptor() ([]byte, []int) {
	return file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDescGZIP(), []int{0, 0}
}

// Container for enum describing possible ad group criterion errors.
type AdGroupCriterionErrorEnum struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *AdGroupCriterionErrorEnum) Reset() {
	*x = AdGroupCriterionErrorEnum{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *AdGroupCriterionErrorEnum) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*AdGroupCriterionErrorEnum) ProtoMessage() {}

func (x *AdGroupCriterionErrorEnum) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use AdGroupCriterionErrorEnum.ProtoReflect.Descriptor instead.
func (*AdGroupCriterionErrorEnum) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDescGZIP(), []int{0}
}

var File_google_ads_googleads_v1_errors_ad_group_criterion_error_proto protoreflect.FileDescriptor

var file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDesc = []byte{
	0x0a, 0x3d, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x31, 0x2f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73,
	0x2f, 0x61, 0x64, 0x5f, 0x67, 0x72, 0x6f, 0x75, 0x70, 0x5f, 0x63, 0x72, 0x69, 0x74, 0x65, 0x72,
	0x69, 0x6f, 0x6e, 0x5f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12,
	0x1e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x31, 0x2e, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x1a,
	0x1c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x61, 0x6e, 0x6e, 0x6f,
	0x74, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22, 0xd7, 0x0c,
	0x0a, 0x19, 0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69,
	0x6f, 0x6e, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x45, 0x6e, 0x75, 0x6d, 0x22, 0xb9, 0x0c, 0x0a, 0x15,
	0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e,
	0x45, 0x72, 0x72, 0x6f, 0x72, 0x12, 0x0f, 0x0a, 0x0b, 0x55, 0x4e, 0x53, 0x50, 0x45, 0x43, 0x49,
	0x46, 0x49, 0x45, 0x44, 0x10, 0x00, 0x12, 0x0b, 0x0a, 0x07, 0x55, 0x4e, 0x4b, 0x4e, 0x4f, 0x57,
	0x4e, 0x10, 0x01, 0x12, 0x2b, 0x0a, 0x27, 0x41, 0x44, 0x5f, 0x47, 0x52, 0x4f, 0x55, 0x50, 0x5f,
	0x43, 0x52, 0x49, 0x54, 0x45, 0x52, 0x49, 0x4f, 0x4e, 0x5f, 0x4c, 0x41, 0x42, 0x45, 0x4c, 0x5f,
	0x44, 0x4f, 0x45, 0x53, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x45, 0x58, 0x49, 0x53, 0x54, 0x10, 0x02,
	0x12, 0x2b, 0x0a, 0x27, 0x41, 0x44, 0x5f, 0x47, 0x52, 0x4f, 0x55, 0x50, 0x5f, 0x43, 0x52, 0x49,
	0x54, 0x45, 0x52, 0x49, 0x4f, 0x4e, 0x5f, 0x4c, 0x41, 0x42, 0x45, 0x4c, 0x5f, 0x41, 0x4c, 0x52,
	0x45, 0x41, 0x44, 0x59, 0x5f, 0x45, 0x58, 0x49, 0x53, 0x54, 0x53, 0x10, 0x03, 0x12, 0x2a, 0x0a,
	0x26, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x41, 0x44, 0x44, 0x5f, 0x4c, 0x41, 0x42, 0x45,
	0x4c, 0x5f, 0x54, 0x4f, 0x5f, 0x4e, 0x45, 0x47, 0x41, 0x54, 0x49, 0x56, 0x45, 0x5f, 0x43, 0x52,
	0x49, 0x54, 0x45, 0x52, 0x49, 0x4f, 0x4e, 0x10, 0x04, 0x12, 0x17, 0x0a, 0x13, 0x54, 0x4f, 0x4f,
	0x5f, 0x4d, 0x41, 0x4e, 0x59, 0x5f, 0x4f, 0x50, 0x45, 0x52, 0x41, 0x54, 0x49, 0x4f, 0x4e, 0x53,
	0x10, 0x05, 0x12, 0x18, 0x0a, 0x14, 0x43, 0x41, 0x4e, 0x54, 0x5f, 0x55, 0x50, 0x44, 0x41, 0x54,
	0x45, 0x5f, 0x4e, 0x45, 0x47, 0x41, 0x54, 0x49, 0x56, 0x45, 0x10, 0x06, 0x12, 0x1a, 0x0a, 0x16,
	0x43, 0x4f, 0x4e, 0x43, 0x52, 0x45, 0x54, 0x45, 0x5f, 0x54, 0x59, 0x50, 0x45, 0x5f, 0x52, 0x45,
	0x51, 0x55, 0x49, 0x52, 0x45, 0x44, 0x10, 0x07, 0x12, 0x21, 0x0a, 0x1d, 0x42, 0x49, 0x44, 0x5f,
	0x49, 0x4e, 0x43, 0x4f, 0x4d, 0x50, 0x41, 0x54, 0x49, 0x42, 0x4c, 0x45, 0x5f, 0x57, 0x49, 0x54,
	0x48, 0x5f, 0x41, 0x44, 0x47, 0x52, 0x4f, 0x55, 0x50, 0x10, 0x08, 0x12, 0x1d, 0x0a, 0x19, 0x43,
	0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x54, 0x41, 0x52, 0x47, 0x45, 0x54, 0x5f, 0x41, 0x4e, 0x44,
	0x5f, 0x45, 0x58, 0x43, 0x4c, 0x55, 0x44, 0x45, 0x10, 0x09, 0x12, 0x0f, 0x0a, 0x0b, 0x49, 0x4c,
	0x4c, 0x45, 0x47, 0x41, 0x4c, 0x5f, 0x55, 0x52, 0x4c, 0x10, 0x0a, 0x12, 0x18, 0x0a, 0x14, 0x49,
	0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x4b, 0x45, 0x59, 0x57, 0x4f, 0x52, 0x44, 0x5f, 0x54,
	0x45, 0x58, 0x54, 0x10, 0x0b, 0x12, 0x1b, 0x0a, 0x17, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44,
	0x5f, 0x44, 0x45, 0x53, 0x54, 0x49, 0x4e, 0x41, 0x54, 0x49, 0x4f, 0x4e, 0x5f, 0x55, 0x52, 0x4c,
	0x10, 0x0c, 0x12, 0x1f, 0x0a, 0x1b, 0x4d, 0x49, 0x53, 0x53, 0x49, 0x4e, 0x47, 0x5f, 0x44, 0x45,
	0x53, 0x54, 0x49, 0x4e, 0x41, 0x54, 0x49, 0x4f, 0x4e, 0x5f, 0x55, 0x52, 0x4c, 0x5f, 0x54, 0x41,
	0x47, 0x10, 0x0d, 0x12, 0x31, 0x0a, 0x2d, 0x4b, 0x45, 0x59, 0x57, 0x4f, 0x52, 0x44, 0x5f, 0x4c,
	0x45, 0x56, 0x45, 0x4c, 0x5f, 0x42, 0x49, 0x44, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x53, 0x55, 0x50,
	0x50, 0x4f, 0x52, 0x54, 0x45, 0x44, 0x5f, 0x46, 0x4f, 0x52, 0x5f, 0x4d, 0x41, 0x4e, 0x55, 0x41,
	0x4c, 0x43, 0x50, 0x4d, 0x10, 0x0e, 0x12, 0x17, 0x0a, 0x13, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49,
	0x44, 0x5f, 0x55, 0x53, 0x45, 0x52, 0x5f, 0x53, 0x54, 0x41, 0x54, 0x55, 0x53, 0x10, 0x0f, 0x12,
	0x1c, 0x0a, 0x18, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x41, 0x44, 0x44, 0x5f, 0x43, 0x52,
	0x49, 0x54, 0x45, 0x52, 0x49, 0x41, 0x5f, 0x54, 0x59, 0x50, 0x45, 0x10, 0x10, 0x12, 0x20, 0x0a,
	0x1c, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x45, 0x58, 0x43, 0x4c, 0x55, 0x44, 0x45, 0x5f,
	0x43, 0x52, 0x49, 0x54, 0x45, 0x52, 0x49, 0x41, 0x5f, 0x54, 0x59, 0x50, 0x45, 0x10, 0x11, 0x12,
	0x35, 0x0a, 0x31, 0x43, 0x41, 0x4d, 0x50, 0x41, 0x49, 0x47, 0x4e, 0x5f, 0x54, 0x59, 0x50, 0x45,
	0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x43, 0x4f, 0x4d, 0x50, 0x41, 0x54, 0x49, 0x42, 0x4c, 0x45, 0x5f,
	0x57, 0x49, 0x54, 0x48, 0x5f, 0x50, 0x41, 0x52, 0x54, 0x49, 0x41, 0x4c, 0x5f, 0x46, 0x41, 0x49,
	0x4c, 0x55, 0x52, 0x45, 0x10, 0x1b, 0x12, 0x2d, 0x0a, 0x29, 0x4f, 0x50, 0x45, 0x52, 0x41, 0x54,
	0x49, 0x4f, 0x4e, 0x53, 0x5f, 0x46, 0x4f, 0x52, 0x5f, 0x54, 0x4f, 0x4f, 0x5f, 0x4d, 0x41, 0x4e,
	0x59, 0x5f, 0x53, 0x48, 0x4f, 0x50, 0x50, 0x49, 0x4e, 0x47, 0x5f, 0x41, 0x44, 0x47, 0x52, 0x4f,
	0x55, 0x50, 0x53, 0x10, 0x1c, 0x12, 0x34, 0x0a, 0x30, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f,
	0x4d, 0x4f, 0x44, 0x49, 0x46, 0x59, 0x5f, 0x55, 0x52, 0x4c, 0x5f, 0x46, 0x49, 0x45, 0x4c, 0x44,
	0x53, 0x5f, 0x57, 0x49, 0x54, 0x48, 0x5f, 0x44, 0x55, 0x50, 0x4c, 0x49, 0x43, 0x41, 0x54, 0x45,
	0x5f, 0x45, 0x4c, 0x45, 0x4d, 0x45, 0x4e, 0x54, 0x53, 0x10, 0x1d, 0x12, 0x21, 0x0a, 0x1d, 0x43,
	0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x53, 0x45, 0x54, 0x5f, 0x57, 0x49, 0x54, 0x48, 0x4f, 0x55,
	0x54, 0x5f, 0x46, 0x49, 0x4e, 0x41, 0x4c, 0x5f, 0x55, 0x52, 0x4c, 0x53, 0x10, 0x1e, 0x12, 0x36,
	0x0a, 0x32, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x43, 0x4c, 0x45, 0x41, 0x52, 0x5f, 0x46,
	0x49, 0x4e, 0x41, 0x4c, 0x5f, 0x55, 0x52, 0x4c, 0x53, 0x5f, 0x49, 0x46, 0x5f, 0x46, 0x49, 0x4e,
	0x41, 0x4c, 0x5f, 0x4d, 0x4f, 0x42, 0x49, 0x4c, 0x45, 0x5f, 0x55, 0x52, 0x4c, 0x53, 0x5f, 0x45,
	0x58, 0x49, 0x53, 0x54, 0x10, 0x1f, 0x12, 0x33, 0x0a, 0x2f, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54,
	0x5f, 0x43, 0x4c, 0x45, 0x41, 0x52, 0x5f, 0x46, 0x49, 0x4e, 0x41, 0x4c, 0x5f, 0x55, 0x52, 0x4c,
	0x53, 0x5f, 0x49, 0x46, 0x5f, 0x46, 0x49, 0x4e, 0x41, 0x4c, 0x5f, 0x41, 0x50, 0x50, 0x5f, 0x55,
	0x52, 0x4c, 0x53, 0x5f, 0x45, 0x58, 0x49, 0x53, 0x54, 0x10, 0x20, 0x12, 0x3b, 0x0a, 0x37, 0x43,
	0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x43, 0x4c, 0x45, 0x41, 0x52, 0x5f, 0x46, 0x49, 0x4e, 0x41,
	0x4c, 0x5f, 0x55, 0x52, 0x4c, 0x53, 0x5f, 0x49, 0x46, 0x5f, 0x54, 0x52, 0x41, 0x43, 0x4b, 0x49,
	0x4e, 0x47, 0x5f, 0x55, 0x52, 0x4c, 0x5f, 0x54, 0x45, 0x4d, 0x50, 0x4c, 0x41, 0x54, 0x45, 0x5f,
	0x45, 0x58, 0x49, 0x53, 0x54, 0x53, 0x10, 0x21, 0x12, 0x3a, 0x0a, 0x36, 0x43, 0x41, 0x4e, 0x4e,
	0x4f, 0x54, 0x5f, 0x43, 0x4c, 0x45, 0x41, 0x52, 0x5f, 0x46, 0x49, 0x4e, 0x41, 0x4c, 0x5f, 0x55,
	0x52, 0x4c, 0x53, 0x5f, 0x49, 0x46, 0x5f, 0x55, 0x52, 0x4c, 0x5f, 0x43, 0x55, 0x53, 0x54, 0x4f,
	0x4d, 0x5f, 0x50, 0x41, 0x52, 0x41, 0x4d, 0x45, 0x54, 0x45, 0x52, 0x53, 0x5f, 0x45, 0x58, 0x49,
	0x53, 0x54, 0x10, 0x22, 0x12, 0x32, 0x0a, 0x2e, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x53,
	0x45, 0x54, 0x5f, 0x42, 0x4f, 0x54, 0x48, 0x5f, 0x44, 0x45, 0x53, 0x54, 0x49, 0x4e, 0x41, 0x54,
	0x49, 0x4f, 0x4e, 0x5f, 0x55, 0x52, 0x4c, 0x5f, 0x41, 0x4e, 0x44, 0x5f, 0x46, 0x49, 0x4e, 0x41,
	0x4c, 0x5f, 0x55, 0x52, 0x4c, 0x53, 0x10, 0x23, 0x12, 0x3d, 0x0a, 0x39, 0x43, 0x41, 0x4e, 0x4e,
	0x4f, 0x54, 0x5f, 0x53, 0x45, 0x54, 0x5f, 0x42, 0x4f, 0x54, 0x48, 0x5f, 0x44, 0x45, 0x53, 0x54,
	0x49, 0x4e, 0x41, 0x54, 0x49, 0x4f, 0x4e, 0x5f, 0x55, 0x52, 0x4c, 0x5f, 0x41, 0x4e, 0x44, 0x5f,
	0x54, 0x52, 0x41, 0x43, 0x4b, 0x49, 0x4e, 0x47, 0x5f, 0x55, 0x52, 0x4c, 0x5f, 0x54, 0x45, 0x4d,
	0x50, 0x4c, 0x41, 0x54, 0x45, 0x10, 0x24, 0x12, 0x2f, 0x0a, 0x2b, 0x46, 0x49, 0x4e, 0x41, 0x4c,
	0x5f, 0x55, 0x52, 0x4c, 0x53, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x53, 0x55, 0x50, 0x50, 0x4f, 0x52,
	0x54, 0x45, 0x44, 0x5f, 0x46, 0x4f, 0x52, 0x5f, 0x43, 0x52, 0x49, 0x54, 0x45, 0x52, 0x49, 0x4f,
	0x4e, 0x5f, 0x54, 0x59, 0x50, 0x45, 0x10, 0x25, 0x12, 0x36, 0x0a, 0x32, 0x46, 0x49, 0x4e, 0x41,
	0x4c, 0x5f, 0x4d, 0x4f, 0x42, 0x49, 0x4c, 0x45, 0x5f, 0x55, 0x52, 0x4c, 0x53, 0x5f, 0x4e, 0x4f,
	0x54, 0x5f, 0x53, 0x55, 0x50, 0x50, 0x4f, 0x52, 0x54, 0x45, 0x44, 0x5f, 0x46, 0x4f, 0x52, 0x5f,
	0x43, 0x52, 0x49, 0x54, 0x45, 0x52, 0x49, 0x4f, 0x4e, 0x5f, 0x54, 0x59, 0x50, 0x45, 0x10, 0x26,
	0x12, 0x23, 0x0a, 0x1f, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x4c, 0x49, 0x53, 0x54,
	0x49, 0x4e, 0x47, 0x5f, 0x47, 0x52, 0x4f, 0x55, 0x50, 0x5f, 0x48, 0x49, 0x45, 0x52, 0x41, 0x52,
	0x43, 0x48, 0x59, 0x10, 0x27, 0x12, 0x2b, 0x0a, 0x27, 0x4c, 0x49, 0x53, 0x54, 0x49, 0x4e, 0x47,
	0x5f, 0x47, 0x52, 0x4f, 0x55, 0x50, 0x5f, 0x55, 0x4e, 0x49, 0x54, 0x5f, 0x43, 0x41, 0x4e, 0x4e,
	0x4f, 0x54, 0x5f, 0x48, 0x41, 0x56, 0x45, 0x5f, 0x43, 0x48, 0x49, 0x4c, 0x44, 0x52, 0x45, 0x4e,
	0x10, 0x28, 0x12, 0x32, 0x0a, 0x2e, 0x4c, 0x49, 0x53, 0x54, 0x49, 0x4e, 0x47, 0x5f, 0x47, 0x52,
	0x4f, 0x55, 0x50, 0x5f, 0x53, 0x55, 0x42, 0x44, 0x49, 0x56, 0x49, 0x53, 0x49, 0x4f, 0x4e, 0x5f,
	0x52, 0x45, 0x51, 0x55, 0x49, 0x52, 0x45, 0x53, 0x5f, 0x4f, 0x54, 0x48, 0x45, 0x52, 0x53, 0x5f,
	0x43, 0x41, 0x53, 0x45, 0x10, 0x29, 0x12, 0x3a, 0x0a, 0x36, 0x4c, 0x49, 0x53, 0x54, 0x49, 0x4e,
	0x47, 0x5f, 0x47, 0x52, 0x4f, 0x55, 0x50, 0x5f, 0x52, 0x45, 0x51, 0x55, 0x49, 0x52, 0x45, 0x53,
	0x5f, 0x53, 0x41, 0x4d, 0x45, 0x5f, 0x44, 0x49, 0x4d, 0x45, 0x4e, 0x53, 0x49, 0x4f, 0x4e, 0x5f,
	0x54, 0x59, 0x50, 0x45, 0x5f, 0x41, 0x53, 0x5f, 0x53, 0x49, 0x42, 0x4c, 0x49, 0x4e, 0x47, 0x53,
	0x10, 0x2a, 0x12, 0x20, 0x0a, 0x1c, 0x4c, 0x49, 0x53, 0x54, 0x49, 0x4e, 0x47, 0x5f, 0x47, 0x52,
	0x4f, 0x55, 0x50, 0x5f, 0x41, 0x4c, 0x52, 0x45, 0x41, 0x44, 0x59, 0x5f, 0x45, 0x58, 0x49, 0x53,
	0x54, 0x53, 0x10, 0x2b, 0x12, 0x20, 0x0a, 0x1c, 0x4c, 0x49, 0x53, 0x54, 0x49, 0x4e, 0x47, 0x5f,
	0x47, 0x52, 0x4f, 0x55, 0x50, 0x5f, 0x44, 0x4f, 0x45, 0x53, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x45,
	0x58, 0x49, 0x53, 0x54, 0x10, 0x2c, 0x12, 0x23, 0x0a, 0x1f, 0x4c, 0x49, 0x53, 0x54, 0x49, 0x4e,
	0x47, 0x5f, 0x47, 0x52, 0x4f, 0x55, 0x50, 0x5f, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x42,
	0x45, 0x5f, 0x52, 0x45, 0x4d, 0x4f, 0x56, 0x45, 0x44, 0x10, 0x2d, 0x12, 0x1e, 0x0a, 0x1a, 0x49,
	0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x4c, 0x49, 0x53, 0x54, 0x49, 0x4e, 0x47, 0x5f, 0x47,
	0x52, 0x4f, 0x55, 0x50, 0x5f, 0x54, 0x59, 0x50, 0x45, 0x10, 0x2e, 0x12, 0x2a, 0x0a, 0x26, 0x4c,
	0x49, 0x53, 0x54, 0x49, 0x4e, 0x47, 0x5f, 0x47, 0x52, 0x4f, 0x55, 0x50, 0x5f, 0x41, 0x44, 0x44,
	0x5f, 0x4d, 0x41, 0x59, 0x5f, 0x4f, 0x4e, 0x4c, 0x59, 0x5f, 0x55, 0x53, 0x45, 0x5f, 0x54, 0x45,
	0x4d, 0x50, 0x5f, 0x49, 0x44, 0x10, 0x2f, 0x42, 0xf5, 0x01, 0x0a, 0x22, 0x63, 0x6f, 0x6d, 0x2e,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x31, 0x2e, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x42, 0x1a,
	0x41, 0x64, 0x47, 0x72, 0x6f, 0x75, 0x70, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69, 0x6f, 0x6e,
	0x45, 0x72, 0x72, 0x6f, 0x72, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a, 0x44, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f,
	0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61,
	0x70, 0x69, 0x73, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64,
	0x73, 0x2f, 0x76, 0x31, 0x2f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x3b, 0x65, 0x72, 0x72, 0x6f,
	0x72, 0x73, 0xa2, 0x02, 0x03, 0x47, 0x41, 0x41, 0xaa, 0x02, 0x1e, 0x47, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x2e, 0x41, 0x64, 0x73, 0x2e, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x2e,
	0x56, 0x31, 0x2e, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x73, 0xca, 0x02, 0x1e, 0x47, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x5c, 0x41, 0x64, 0x73, 0x5c, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73,
	0x5c, 0x56, 0x31, 0x5c, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x73, 0xea, 0x02, 0x22, 0x47, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x3a, 0x3a, 0x41, 0x64, 0x73, 0x3a, 0x3a, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x41, 0x64, 0x73, 0x3a, 0x3a, 0x56, 0x31, 0x3a, 0x3a, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x62,
	0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDescOnce sync.Once
	file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDescData = file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDesc
)

func file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDescGZIP() []byte {
	file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDescOnce.Do(func() {
		file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDescData)
	})
	return file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDescData
}

var file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_enumTypes = make([]protoimpl.EnumInfo, 1)
var file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_goTypes = []interface{}{
	(AdGroupCriterionErrorEnum_AdGroupCriterionError)(0), // 0: google.ads.googleads.v1.errors.AdGroupCriterionErrorEnum.AdGroupCriterionError
	(*AdGroupCriterionErrorEnum)(nil),                    // 1: google.ads.googleads.v1.errors.AdGroupCriterionErrorEnum
}
var file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_depIdxs = []int32{
	0, // [0:0] is the sub-list for method output_type
	0, // [0:0] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() { file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_init() }
func file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_init() {
	if File_google_ads_googleads_v1_errors_ad_group_criterion_error_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*AdGroupCriterionErrorEnum); i {
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
			RawDescriptor: file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDesc,
			NumEnums:      1,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_goTypes,
		DependencyIndexes: file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_depIdxs,
		EnumInfos:         file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_enumTypes,
		MessageInfos:      file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_msgTypes,
	}.Build()
	File_google_ads_googleads_v1_errors_ad_group_criterion_error_proto = out.File
	file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_rawDesc = nil
	file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_goTypes = nil
	file_google_ads_googleads_v1_errors_ad_group_criterion_error_proto_depIdxs = nil
}
