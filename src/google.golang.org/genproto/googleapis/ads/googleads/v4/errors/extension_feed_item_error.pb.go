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
// source: google/ads/googleads/v4/errors/extension_feed_item_error.proto

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

// Enum describing possible extension feed item errors.
type ExtensionFeedItemErrorEnum_ExtensionFeedItemError int32

const (
	// Enum unspecified.
	ExtensionFeedItemErrorEnum_UNSPECIFIED ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 0
	// The received error code is not known in this version.
	ExtensionFeedItemErrorEnum_UNKNOWN ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 1
	// Value is not within the accepted range.
	ExtensionFeedItemErrorEnum_VALUE_OUT_OF_RANGE ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 2
	// Url list is too long.
	ExtensionFeedItemErrorEnum_URL_LIST_TOO_LONG ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 3
	// Cannot have a geo targeting restriction without having geo targeting.
	ExtensionFeedItemErrorEnum_CANNOT_HAVE_RESTRICTION_ON_EMPTY_GEO_TARGETING ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 4
	// Cannot simultaneously set sitelink field with final urls.
	ExtensionFeedItemErrorEnum_CANNOT_SET_WITH_FINAL_URLS ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 5
	// Must set field with final urls.
	ExtensionFeedItemErrorEnum_CANNOT_SET_WITHOUT_FINAL_URLS ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 6
	// Phone number for a call extension is invalid.
	ExtensionFeedItemErrorEnum_INVALID_PHONE_NUMBER ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 7
	// Phone number for a call extension is not supported for the given country
	// code.
	ExtensionFeedItemErrorEnum_PHONE_NUMBER_NOT_SUPPORTED_FOR_COUNTRY ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 8
	// A carrier specific number in short format is not allowed for call
	// extensions.
	ExtensionFeedItemErrorEnum_CARRIER_SPECIFIC_SHORT_NUMBER_NOT_ALLOWED ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 9
	// Premium rate numbers are not allowed for call extensions.
	ExtensionFeedItemErrorEnum_PREMIUM_RATE_NUMBER_NOT_ALLOWED ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 10
	// Phone number type for a call extension is not allowed.
	// For example, personal number is not allowed for a call extension in
	// most regions.
	ExtensionFeedItemErrorEnum_DISALLOWED_NUMBER_TYPE ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 11
	// Phone number for a call extension does not meet domestic format
	// requirements.
	ExtensionFeedItemErrorEnum_INVALID_DOMESTIC_PHONE_NUMBER_FORMAT ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 12
	// Vanity phone numbers (i.e. those including letters) are not allowed for
	// call extensions.
	ExtensionFeedItemErrorEnum_VANITY_PHONE_NUMBER_NOT_ALLOWED ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 13
	// Call conversion action provided for a call extension is invalid.
	ExtensionFeedItemErrorEnum_INVALID_CALL_CONVERSION_ACTION ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 14
	// For a call extension, the customer is not whitelisted for call tracking.
	ExtensionFeedItemErrorEnum_CUSTOMER_NOT_WHITELISTED_FOR_CALLTRACKING ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 15
	// Call tracking is not supported for the given country for a call
	// extension.
	ExtensionFeedItemErrorEnum_CALLTRACKING_NOT_SUPPORTED_FOR_COUNTRY ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 16
	// Customer hasn't consented for call recording, which is required for
	// creating/updating call feed items. Please see
	// https://support.google.com/google-ads/answer/7412639.
	ExtensionFeedItemErrorEnum_CUSTOMER_CONSENT_FOR_CALL_RECORDING_REQUIRED ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 17
	// App id provided for an app extension is invalid.
	ExtensionFeedItemErrorEnum_INVALID_APP_ID ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 18
	// Quotation marks present in the review text for a review extension.
	ExtensionFeedItemErrorEnum_QUOTES_IN_REVIEW_EXTENSION_SNIPPET ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 19
	// Hyphen character present in the review text for a review extension.
	ExtensionFeedItemErrorEnum_HYPHENS_IN_REVIEW_EXTENSION_SNIPPET ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 20
	// A blacklisted review source name or url was provided for a review
	// extension.
	ExtensionFeedItemErrorEnum_REVIEW_EXTENSION_SOURCE_INELIGIBLE ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 21
	// Review source name should not be found in the review text.
	ExtensionFeedItemErrorEnum_SOURCE_NAME_IN_REVIEW_EXTENSION_TEXT ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 22
	// Inconsistent currency codes.
	ExtensionFeedItemErrorEnum_INCONSISTENT_CURRENCY_CODES ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 23
	// Price extension cannot have duplicated headers.
	ExtensionFeedItemErrorEnum_PRICE_EXTENSION_HAS_DUPLICATED_HEADERS ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 24
	// Price item cannot have duplicated header and description.
	ExtensionFeedItemErrorEnum_PRICE_ITEM_HAS_DUPLICATED_HEADER_AND_DESCRIPTION ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 25
	// Price extension has too few items.
	ExtensionFeedItemErrorEnum_PRICE_EXTENSION_HAS_TOO_FEW_ITEMS ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 26
	// Price extension has too many items.
	ExtensionFeedItemErrorEnum_PRICE_EXTENSION_HAS_TOO_MANY_ITEMS ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 27
	// The input value is not currently supported.
	ExtensionFeedItemErrorEnum_UNSUPPORTED_VALUE ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 28
	// The input value is not currently supported in the selected language of an
	// extension.
	ExtensionFeedItemErrorEnum_UNSUPPORTED_VALUE_IN_SELECTED_LANGUAGE ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 29
	// Unknown or unsupported device preference.
	ExtensionFeedItemErrorEnum_INVALID_DEVICE_PREFERENCE ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 30
	// Invalid feed item schedule end time (i.e., endHour = 24 and endMinute !=
	// 0).
	ExtensionFeedItemErrorEnum_INVALID_SCHEDULE_END ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 31
	// Date time zone does not match the account's time zone.
	ExtensionFeedItemErrorEnum_DATE_TIME_MUST_BE_IN_ACCOUNT_TIME_ZONE ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 32
	// Invalid structured snippet header.
	ExtensionFeedItemErrorEnum_INVALID_SNIPPETS_HEADER ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 33
	// Cannot operate on removed feed item.
	ExtensionFeedItemErrorEnum_CANNOT_OPERATE_ON_REMOVED_FEED_ITEM ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 34
	// Phone number not supported when call tracking enabled for country.
	ExtensionFeedItemErrorEnum_PHONE_NUMBER_NOT_SUPPORTED_WITH_CALLTRACKING_FOR_COUNTRY ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 35
	// Cannot set call_conversion_action while call_conversion_tracking_enabled
	// is set to true.
	ExtensionFeedItemErrorEnum_CONFLICTING_CALL_CONVERSION_SETTINGS ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 36
	// The type of the input extension feed item doesn't match the existing
	// extension feed item.
	ExtensionFeedItemErrorEnum_EXTENSION_TYPE_MISMATCH ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 37
	// The oneof field extension i.e. subtype of extension feed item is
	// required.
	ExtensionFeedItemErrorEnum_EXTENSION_SUBTYPE_REQUIRED ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 38
	// The referenced feed item is not mapped to a supported extension type.
	ExtensionFeedItemErrorEnum_EXTENSION_TYPE_UNSUPPORTED ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 39
	// Cannot operate on a Feed with more than one active FeedMapping.
	ExtensionFeedItemErrorEnum_CANNOT_OPERATE_ON_FEED_WITH_MULTIPLE_MAPPINGS ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 40
	// Cannot operate on a Feed that has key attributes.
	ExtensionFeedItemErrorEnum_CANNOT_OPERATE_ON_FEED_WITH_KEY_ATTRIBUTES ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 41
	// Input price is not in a valid format.
	ExtensionFeedItemErrorEnum_INVALID_PRICE_FORMAT ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 42
	// The promotion time is invalid.
	ExtensionFeedItemErrorEnum_PROMOTION_INVALID_TIME ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 43
	// This field has too many decimal places specified.
	ExtensionFeedItemErrorEnum_TOO_MANY_DECIMAL_PLACES_SPECIFIED ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 44
	// Concrete sub type of ExtensionFeedItem is required for this operation.
	ExtensionFeedItemErrorEnum_CONCRETE_EXTENSION_TYPE_REQUIRED ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 45
	// Feed item schedule end time must be after start time.
	ExtensionFeedItemErrorEnum_SCHEDULE_END_NOT_AFTER_START ExtensionFeedItemErrorEnum_ExtensionFeedItemError = 46
)

// Enum value maps for ExtensionFeedItemErrorEnum_ExtensionFeedItemError.
var (
	ExtensionFeedItemErrorEnum_ExtensionFeedItemError_name = map[int32]string{
		0:  "UNSPECIFIED",
		1:  "UNKNOWN",
		2:  "VALUE_OUT_OF_RANGE",
		3:  "URL_LIST_TOO_LONG",
		4:  "CANNOT_HAVE_RESTRICTION_ON_EMPTY_GEO_TARGETING",
		5:  "CANNOT_SET_WITH_FINAL_URLS",
		6:  "CANNOT_SET_WITHOUT_FINAL_URLS",
		7:  "INVALID_PHONE_NUMBER",
		8:  "PHONE_NUMBER_NOT_SUPPORTED_FOR_COUNTRY",
		9:  "CARRIER_SPECIFIC_SHORT_NUMBER_NOT_ALLOWED",
		10: "PREMIUM_RATE_NUMBER_NOT_ALLOWED",
		11: "DISALLOWED_NUMBER_TYPE",
		12: "INVALID_DOMESTIC_PHONE_NUMBER_FORMAT",
		13: "VANITY_PHONE_NUMBER_NOT_ALLOWED",
		14: "INVALID_CALL_CONVERSION_ACTION",
		15: "CUSTOMER_NOT_WHITELISTED_FOR_CALLTRACKING",
		16: "CALLTRACKING_NOT_SUPPORTED_FOR_COUNTRY",
		17: "CUSTOMER_CONSENT_FOR_CALL_RECORDING_REQUIRED",
		18: "INVALID_APP_ID",
		19: "QUOTES_IN_REVIEW_EXTENSION_SNIPPET",
		20: "HYPHENS_IN_REVIEW_EXTENSION_SNIPPET",
		21: "REVIEW_EXTENSION_SOURCE_INELIGIBLE",
		22: "SOURCE_NAME_IN_REVIEW_EXTENSION_TEXT",
		23: "INCONSISTENT_CURRENCY_CODES",
		24: "PRICE_EXTENSION_HAS_DUPLICATED_HEADERS",
		25: "PRICE_ITEM_HAS_DUPLICATED_HEADER_AND_DESCRIPTION",
		26: "PRICE_EXTENSION_HAS_TOO_FEW_ITEMS",
		27: "PRICE_EXTENSION_HAS_TOO_MANY_ITEMS",
		28: "UNSUPPORTED_VALUE",
		29: "UNSUPPORTED_VALUE_IN_SELECTED_LANGUAGE",
		30: "INVALID_DEVICE_PREFERENCE",
		31: "INVALID_SCHEDULE_END",
		32: "DATE_TIME_MUST_BE_IN_ACCOUNT_TIME_ZONE",
		33: "INVALID_SNIPPETS_HEADER",
		34: "CANNOT_OPERATE_ON_REMOVED_FEED_ITEM",
		35: "PHONE_NUMBER_NOT_SUPPORTED_WITH_CALLTRACKING_FOR_COUNTRY",
		36: "CONFLICTING_CALL_CONVERSION_SETTINGS",
		37: "EXTENSION_TYPE_MISMATCH",
		38: "EXTENSION_SUBTYPE_REQUIRED",
		39: "EXTENSION_TYPE_UNSUPPORTED",
		40: "CANNOT_OPERATE_ON_FEED_WITH_MULTIPLE_MAPPINGS",
		41: "CANNOT_OPERATE_ON_FEED_WITH_KEY_ATTRIBUTES",
		42: "INVALID_PRICE_FORMAT",
		43: "PROMOTION_INVALID_TIME",
		44: "TOO_MANY_DECIMAL_PLACES_SPECIFIED",
		45: "CONCRETE_EXTENSION_TYPE_REQUIRED",
		46: "SCHEDULE_END_NOT_AFTER_START",
	}
	ExtensionFeedItemErrorEnum_ExtensionFeedItemError_value = map[string]int32{
		"UNSPECIFIED":        0,
		"UNKNOWN":            1,
		"VALUE_OUT_OF_RANGE": 2,
		"URL_LIST_TOO_LONG":  3,
		"CANNOT_HAVE_RESTRICTION_ON_EMPTY_GEO_TARGETING":           4,
		"CANNOT_SET_WITH_FINAL_URLS":                               5,
		"CANNOT_SET_WITHOUT_FINAL_URLS":                            6,
		"INVALID_PHONE_NUMBER":                                     7,
		"PHONE_NUMBER_NOT_SUPPORTED_FOR_COUNTRY":                   8,
		"CARRIER_SPECIFIC_SHORT_NUMBER_NOT_ALLOWED":                9,
		"PREMIUM_RATE_NUMBER_NOT_ALLOWED":                          10,
		"DISALLOWED_NUMBER_TYPE":                                   11,
		"INVALID_DOMESTIC_PHONE_NUMBER_FORMAT":                     12,
		"VANITY_PHONE_NUMBER_NOT_ALLOWED":                          13,
		"INVALID_CALL_CONVERSION_ACTION":                           14,
		"CUSTOMER_NOT_WHITELISTED_FOR_CALLTRACKING":                15,
		"CALLTRACKING_NOT_SUPPORTED_FOR_COUNTRY":                   16,
		"CUSTOMER_CONSENT_FOR_CALL_RECORDING_REQUIRED":             17,
		"INVALID_APP_ID":                                           18,
		"QUOTES_IN_REVIEW_EXTENSION_SNIPPET":                       19,
		"HYPHENS_IN_REVIEW_EXTENSION_SNIPPET":                      20,
		"REVIEW_EXTENSION_SOURCE_INELIGIBLE":                       21,
		"SOURCE_NAME_IN_REVIEW_EXTENSION_TEXT":                     22,
		"INCONSISTENT_CURRENCY_CODES":                              23,
		"PRICE_EXTENSION_HAS_DUPLICATED_HEADERS":                   24,
		"PRICE_ITEM_HAS_DUPLICATED_HEADER_AND_DESCRIPTION":         25,
		"PRICE_EXTENSION_HAS_TOO_FEW_ITEMS":                        26,
		"PRICE_EXTENSION_HAS_TOO_MANY_ITEMS":                       27,
		"UNSUPPORTED_VALUE":                                        28,
		"UNSUPPORTED_VALUE_IN_SELECTED_LANGUAGE":                   29,
		"INVALID_DEVICE_PREFERENCE":                                30,
		"INVALID_SCHEDULE_END":                                     31,
		"DATE_TIME_MUST_BE_IN_ACCOUNT_TIME_ZONE":                   32,
		"INVALID_SNIPPETS_HEADER":                                  33,
		"CANNOT_OPERATE_ON_REMOVED_FEED_ITEM":                      34,
		"PHONE_NUMBER_NOT_SUPPORTED_WITH_CALLTRACKING_FOR_COUNTRY": 35,
		"CONFLICTING_CALL_CONVERSION_SETTINGS":                     36,
		"EXTENSION_TYPE_MISMATCH":                                  37,
		"EXTENSION_SUBTYPE_REQUIRED":                               38,
		"EXTENSION_TYPE_UNSUPPORTED":                               39,
		"CANNOT_OPERATE_ON_FEED_WITH_MULTIPLE_MAPPINGS":            40,
		"CANNOT_OPERATE_ON_FEED_WITH_KEY_ATTRIBUTES":               41,
		"INVALID_PRICE_FORMAT":                                     42,
		"PROMOTION_INVALID_TIME":                                   43,
		"TOO_MANY_DECIMAL_PLACES_SPECIFIED":                        44,
		"CONCRETE_EXTENSION_TYPE_REQUIRED":                         45,
		"SCHEDULE_END_NOT_AFTER_START":                             46,
	}
)

func (x ExtensionFeedItemErrorEnum_ExtensionFeedItemError) Enum() *ExtensionFeedItemErrorEnum_ExtensionFeedItemError {
	p := new(ExtensionFeedItemErrorEnum_ExtensionFeedItemError)
	*p = x
	return p
}

func (x ExtensionFeedItemErrorEnum_ExtensionFeedItemError) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (ExtensionFeedItemErrorEnum_ExtensionFeedItemError) Descriptor() protoreflect.EnumDescriptor {
	return file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_enumTypes[0].Descriptor()
}

func (ExtensionFeedItemErrorEnum_ExtensionFeedItemError) Type() protoreflect.EnumType {
	return &file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_enumTypes[0]
}

func (x ExtensionFeedItemErrorEnum_ExtensionFeedItemError) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use ExtensionFeedItemErrorEnum_ExtensionFeedItemError.Descriptor instead.
func (ExtensionFeedItemErrorEnum_ExtensionFeedItemError) EnumDescriptor() ([]byte, []int) {
	return file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDescGZIP(), []int{0, 0}
}

// Container for enum describing possible extension feed item error.
type ExtensionFeedItemErrorEnum struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields
}

func (x *ExtensionFeedItemErrorEnum) Reset() {
	*x = ExtensionFeedItemErrorEnum{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *ExtensionFeedItemErrorEnum) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*ExtensionFeedItemErrorEnum) ProtoMessage() {}

func (x *ExtensionFeedItemErrorEnum) ProtoReflect() protoreflect.Message {
	mi := &file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use ExtensionFeedItemErrorEnum.ProtoReflect.Descriptor instead.
func (*ExtensionFeedItemErrorEnum) Descriptor() ([]byte, []int) {
	return file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDescGZIP(), []int{0}
}

var File_google_ads_googleads_v4_errors_extension_feed_item_error_proto protoreflect.FileDescriptor

var file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDesc = []byte{
	0x0a, 0x3e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2f, 0x76, 0x34, 0x2f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73,
	0x2f, 0x65, 0x78, 0x74, 0x65, 0x6e, 0x73, 0x69, 0x6f, 0x6e, 0x5f, 0x66, 0x65, 0x65, 0x64, 0x5f,
	0x69, 0x74, 0x65, 0x6d, 0x5f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f,
	0x12, 0x1e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73,
	0x1a, 0x1c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x61, 0x6e, 0x6e,
	0x6f, 0x74, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22, 0xf5,
	0x0d, 0x0a, 0x1a, 0x45, 0x78, 0x74, 0x65, 0x6e, 0x73, 0x69, 0x6f, 0x6e, 0x46, 0x65, 0x65, 0x64,
	0x49, 0x74, 0x65, 0x6d, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x45, 0x6e, 0x75, 0x6d, 0x22, 0xd6, 0x0d,
	0x0a, 0x16, 0x45, 0x78, 0x74, 0x65, 0x6e, 0x73, 0x69, 0x6f, 0x6e, 0x46, 0x65, 0x65, 0x64, 0x49,
	0x74, 0x65, 0x6d, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x12, 0x0f, 0x0a, 0x0b, 0x55, 0x4e, 0x53, 0x50,
	0x45, 0x43, 0x49, 0x46, 0x49, 0x45, 0x44, 0x10, 0x00, 0x12, 0x0b, 0x0a, 0x07, 0x55, 0x4e, 0x4b,
	0x4e, 0x4f, 0x57, 0x4e, 0x10, 0x01, 0x12, 0x16, 0x0a, 0x12, 0x56, 0x41, 0x4c, 0x55, 0x45, 0x5f,
	0x4f, 0x55, 0x54, 0x5f, 0x4f, 0x46, 0x5f, 0x52, 0x41, 0x4e, 0x47, 0x45, 0x10, 0x02, 0x12, 0x15,
	0x0a, 0x11, 0x55, 0x52, 0x4c, 0x5f, 0x4c, 0x49, 0x53, 0x54, 0x5f, 0x54, 0x4f, 0x4f, 0x5f, 0x4c,
	0x4f, 0x4e, 0x47, 0x10, 0x03, 0x12, 0x32, 0x0a, 0x2e, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f,
	0x48, 0x41, 0x56, 0x45, 0x5f, 0x52, 0x45, 0x53, 0x54, 0x52, 0x49, 0x43, 0x54, 0x49, 0x4f, 0x4e,
	0x5f, 0x4f, 0x4e, 0x5f, 0x45, 0x4d, 0x50, 0x54, 0x59, 0x5f, 0x47, 0x45, 0x4f, 0x5f, 0x54, 0x41,
	0x52, 0x47, 0x45, 0x54, 0x49, 0x4e, 0x47, 0x10, 0x04, 0x12, 0x1e, 0x0a, 0x1a, 0x43, 0x41, 0x4e,
	0x4e, 0x4f, 0x54, 0x5f, 0x53, 0x45, 0x54, 0x5f, 0x57, 0x49, 0x54, 0x48, 0x5f, 0x46, 0x49, 0x4e,
	0x41, 0x4c, 0x5f, 0x55, 0x52, 0x4c, 0x53, 0x10, 0x05, 0x12, 0x21, 0x0a, 0x1d, 0x43, 0x41, 0x4e,
	0x4e, 0x4f, 0x54, 0x5f, 0x53, 0x45, 0x54, 0x5f, 0x57, 0x49, 0x54, 0x48, 0x4f, 0x55, 0x54, 0x5f,
	0x46, 0x49, 0x4e, 0x41, 0x4c, 0x5f, 0x55, 0x52, 0x4c, 0x53, 0x10, 0x06, 0x12, 0x18, 0x0a, 0x14,
	0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x50, 0x48, 0x4f, 0x4e, 0x45, 0x5f, 0x4e, 0x55,
	0x4d, 0x42, 0x45, 0x52, 0x10, 0x07, 0x12, 0x2a, 0x0a, 0x26, 0x50, 0x48, 0x4f, 0x4e, 0x45, 0x5f,
	0x4e, 0x55, 0x4d, 0x42, 0x45, 0x52, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x53, 0x55, 0x50, 0x50, 0x4f,
	0x52, 0x54, 0x45, 0x44, 0x5f, 0x46, 0x4f, 0x52, 0x5f, 0x43, 0x4f, 0x55, 0x4e, 0x54, 0x52, 0x59,
	0x10, 0x08, 0x12, 0x2d, 0x0a, 0x29, 0x43, 0x41, 0x52, 0x52, 0x49, 0x45, 0x52, 0x5f, 0x53, 0x50,
	0x45, 0x43, 0x49, 0x46, 0x49, 0x43, 0x5f, 0x53, 0x48, 0x4f, 0x52, 0x54, 0x5f, 0x4e, 0x55, 0x4d,
	0x42, 0x45, 0x52, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x41, 0x4c, 0x4c, 0x4f, 0x57, 0x45, 0x44, 0x10,
	0x09, 0x12, 0x23, 0x0a, 0x1f, 0x50, 0x52, 0x45, 0x4d, 0x49, 0x55, 0x4d, 0x5f, 0x52, 0x41, 0x54,
	0x45, 0x5f, 0x4e, 0x55, 0x4d, 0x42, 0x45, 0x52, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x41, 0x4c, 0x4c,
	0x4f, 0x57, 0x45, 0x44, 0x10, 0x0a, 0x12, 0x1a, 0x0a, 0x16, 0x44, 0x49, 0x53, 0x41, 0x4c, 0x4c,
	0x4f, 0x57, 0x45, 0x44, 0x5f, 0x4e, 0x55, 0x4d, 0x42, 0x45, 0x52, 0x5f, 0x54, 0x59, 0x50, 0x45,
	0x10, 0x0b, 0x12, 0x28, 0x0a, 0x24, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x44, 0x4f,
	0x4d, 0x45, 0x53, 0x54, 0x49, 0x43, 0x5f, 0x50, 0x48, 0x4f, 0x4e, 0x45, 0x5f, 0x4e, 0x55, 0x4d,
	0x42, 0x45, 0x52, 0x5f, 0x46, 0x4f, 0x52, 0x4d, 0x41, 0x54, 0x10, 0x0c, 0x12, 0x23, 0x0a, 0x1f,
	0x56, 0x41, 0x4e, 0x49, 0x54, 0x59, 0x5f, 0x50, 0x48, 0x4f, 0x4e, 0x45, 0x5f, 0x4e, 0x55, 0x4d,
	0x42, 0x45, 0x52, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x41, 0x4c, 0x4c, 0x4f, 0x57, 0x45, 0x44, 0x10,
	0x0d, 0x12, 0x22, 0x0a, 0x1e, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x43, 0x41, 0x4c,
	0x4c, 0x5f, 0x43, 0x4f, 0x4e, 0x56, 0x45, 0x52, 0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x41, 0x43, 0x54,
	0x49, 0x4f, 0x4e, 0x10, 0x0e, 0x12, 0x2d, 0x0a, 0x29, 0x43, 0x55, 0x53, 0x54, 0x4f, 0x4d, 0x45,
	0x52, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x57, 0x48, 0x49, 0x54, 0x45, 0x4c, 0x49, 0x53, 0x54, 0x45,
	0x44, 0x5f, 0x46, 0x4f, 0x52, 0x5f, 0x43, 0x41, 0x4c, 0x4c, 0x54, 0x52, 0x41, 0x43, 0x4b, 0x49,
	0x4e, 0x47, 0x10, 0x0f, 0x12, 0x2a, 0x0a, 0x26, 0x43, 0x41, 0x4c, 0x4c, 0x54, 0x52, 0x41, 0x43,
	0x4b, 0x49, 0x4e, 0x47, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x53, 0x55, 0x50, 0x50, 0x4f, 0x52, 0x54,
	0x45, 0x44, 0x5f, 0x46, 0x4f, 0x52, 0x5f, 0x43, 0x4f, 0x55, 0x4e, 0x54, 0x52, 0x59, 0x10, 0x10,
	0x12, 0x30, 0x0a, 0x2c, 0x43, 0x55, 0x53, 0x54, 0x4f, 0x4d, 0x45, 0x52, 0x5f, 0x43, 0x4f, 0x4e,
	0x53, 0x45, 0x4e, 0x54, 0x5f, 0x46, 0x4f, 0x52, 0x5f, 0x43, 0x41, 0x4c, 0x4c, 0x5f, 0x52, 0x45,
	0x43, 0x4f, 0x52, 0x44, 0x49, 0x4e, 0x47, 0x5f, 0x52, 0x45, 0x51, 0x55, 0x49, 0x52, 0x45, 0x44,
	0x10, 0x11, 0x12, 0x12, 0x0a, 0x0e, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x41, 0x50,
	0x50, 0x5f, 0x49, 0x44, 0x10, 0x12, 0x12, 0x26, 0x0a, 0x22, 0x51, 0x55, 0x4f, 0x54, 0x45, 0x53,
	0x5f, 0x49, 0x4e, 0x5f, 0x52, 0x45, 0x56, 0x49, 0x45, 0x57, 0x5f, 0x45, 0x58, 0x54, 0x45, 0x4e,
	0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x53, 0x4e, 0x49, 0x50, 0x50, 0x45, 0x54, 0x10, 0x13, 0x12, 0x27,
	0x0a, 0x23, 0x48, 0x59, 0x50, 0x48, 0x45, 0x4e, 0x53, 0x5f, 0x49, 0x4e, 0x5f, 0x52, 0x45, 0x56,
	0x49, 0x45, 0x57, 0x5f, 0x45, 0x58, 0x54, 0x45, 0x4e, 0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x53, 0x4e,
	0x49, 0x50, 0x50, 0x45, 0x54, 0x10, 0x14, 0x12, 0x26, 0x0a, 0x22, 0x52, 0x45, 0x56, 0x49, 0x45,
	0x57, 0x5f, 0x45, 0x58, 0x54, 0x45, 0x4e, 0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x53, 0x4f, 0x55, 0x52,
	0x43, 0x45, 0x5f, 0x49, 0x4e, 0x45, 0x4c, 0x49, 0x47, 0x49, 0x42, 0x4c, 0x45, 0x10, 0x15, 0x12,
	0x28, 0x0a, 0x24, 0x53, 0x4f, 0x55, 0x52, 0x43, 0x45, 0x5f, 0x4e, 0x41, 0x4d, 0x45, 0x5f, 0x49,
	0x4e, 0x5f, 0x52, 0x45, 0x56, 0x49, 0x45, 0x57, 0x5f, 0x45, 0x58, 0x54, 0x45, 0x4e, 0x53, 0x49,
	0x4f, 0x4e, 0x5f, 0x54, 0x45, 0x58, 0x54, 0x10, 0x16, 0x12, 0x1f, 0x0a, 0x1b, 0x49, 0x4e, 0x43,
	0x4f, 0x4e, 0x53, 0x49, 0x53, 0x54, 0x45, 0x4e, 0x54, 0x5f, 0x43, 0x55, 0x52, 0x52, 0x45, 0x4e,
	0x43, 0x59, 0x5f, 0x43, 0x4f, 0x44, 0x45, 0x53, 0x10, 0x17, 0x12, 0x2a, 0x0a, 0x26, 0x50, 0x52,
	0x49, 0x43, 0x45, 0x5f, 0x45, 0x58, 0x54, 0x45, 0x4e, 0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x48, 0x41,
	0x53, 0x5f, 0x44, 0x55, 0x50, 0x4c, 0x49, 0x43, 0x41, 0x54, 0x45, 0x44, 0x5f, 0x48, 0x45, 0x41,
	0x44, 0x45, 0x52, 0x53, 0x10, 0x18, 0x12, 0x34, 0x0a, 0x30, 0x50, 0x52, 0x49, 0x43, 0x45, 0x5f,
	0x49, 0x54, 0x45, 0x4d, 0x5f, 0x48, 0x41, 0x53, 0x5f, 0x44, 0x55, 0x50, 0x4c, 0x49, 0x43, 0x41,
	0x54, 0x45, 0x44, 0x5f, 0x48, 0x45, 0x41, 0x44, 0x45, 0x52, 0x5f, 0x41, 0x4e, 0x44, 0x5f, 0x44,
	0x45, 0x53, 0x43, 0x52, 0x49, 0x50, 0x54, 0x49, 0x4f, 0x4e, 0x10, 0x19, 0x12, 0x25, 0x0a, 0x21,
	0x50, 0x52, 0x49, 0x43, 0x45, 0x5f, 0x45, 0x58, 0x54, 0x45, 0x4e, 0x53, 0x49, 0x4f, 0x4e, 0x5f,
	0x48, 0x41, 0x53, 0x5f, 0x54, 0x4f, 0x4f, 0x5f, 0x46, 0x45, 0x57, 0x5f, 0x49, 0x54, 0x45, 0x4d,
	0x53, 0x10, 0x1a, 0x12, 0x26, 0x0a, 0x22, 0x50, 0x52, 0x49, 0x43, 0x45, 0x5f, 0x45, 0x58, 0x54,
	0x45, 0x4e, 0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x48, 0x41, 0x53, 0x5f, 0x54, 0x4f, 0x4f, 0x5f, 0x4d,
	0x41, 0x4e, 0x59, 0x5f, 0x49, 0x54, 0x45, 0x4d, 0x53, 0x10, 0x1b, 0x12, 0x15, 0x0a, 0x11, 0x55,
	0x4e, 0x53, 0x55, 0x50, 0x50, 0x4f, 0x52, 0x54, 0x45, 0x44, 0x5f, 0x56, 0x41, 0x4c, 0x55, 0x45,
	0x10, 0x1c, 0x12, 0x2a, 0x0a, 0x26, 0x55, 0x4e, 0x53, 0x55, 0x50, 0x50, 0x4f, 0x52, 0x54, 0x45,
	0x44, 0x5f, 0x56, 0x41, 0x4c, 0x55, 0x45, 0x5f, 0x49, 0x4e, 0x5f, 0x53, 0x45, 0x4c, 0x45, 0x43,
	0x54, 0x45, 0x44, 0x5f, 0x4c, 0x41, 0x4e, 0x47, 0x55, 0x41, 0x47, 0x45, 0x10, 0x1d, 0x12, 0x1d,
	0x0a, 0x19, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x44, 0x45, 0x56, 0x49, 0x43, 0x45,
	0x5f, 0x50, 0x52, 0x45, 0x46, 0x45, 0x52, 0x45, 0x4e, 0x43, 0x45, 0x10, 0x1e, 0x12, 0x18, 0x0a,
	0x14, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x53, 0x43, 0x48, 0x45, 0x44, 0x55, 0x4c,
	0x45, 0x5f, 0x45, 0x4e, 0x44, 0x10, 0x1f, 0x12, 0x2a, 0x0a, 0x26, 0x44, 0x41, 0x54, 0x45, 0x5f,
	0x54, 0x49, 0x4d, 0x45, 0x5f, 0x4d, 0x55, 0x53, 0x54, 0x5f, 0x42, 0x45, 0x5f, 0x49, 0x4e, 0x5f,
	0x41, 0x43, 0x43, 0x4f, 0x55, 0x4e, 0x54, 0x5f, 0x54, 0x49, 0x4d, 0x45, 0x5f, 0x5a, 0x4f, 0x4e,
	0x45, 0x10, 0x20, 0x12, 0x1b, 0x0a, 0x17, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x53,
	0x4e, 0x49, 0x50, 0x50, 0x45, 0x54, 0x53, 0x5f, 0x48, 0x45, 0x41, 0x44, 0x45, 0x52, 0x10, 0x21,
	0x12, 0x27, 0x0a, 0x23, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x4f, 0x50, 0x45, 0x52, 0x41,
	0x54, 0x45, 0x5f, 0x4f, 0x4e, 0x5f, 0x52, 0x45, 0x4d, 0x4f, 0x56, 0x45, 0x44, 0x5f, 0x46, 0x45,
	0x45, 0x44, 0x5f, 0x49, 0x54, 0x45, 0x4d, 0x10, 0x22, 0x12, 0x3c, 0x0a, 0x38, 0x50, 0x48, 0x4f,
	0x4e, 0x45, 0x5f, 0x4e, 0x55, 0x4d, 0x42, 0x45, 0x52, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x53, 0x55,
	0x50, 0x50, 0x4f, 0x52, 0x54, 0x45, 0x44, 0x5f, 0x57, 0x49, 0x54, 0x48, 0x5f, 0x43, 0x41, 0x4c,
	0x4c, 0x54, 0x52, 0x41, 0x43, 0x4b, 0x49, 0x4e, 0x47, 0x5f, 0x46, 0x4f, 0x52, 0x5f, 0x43, 0x4f,
	0x55, 0x4e, 0x54, 0x52, 0x59, 0x10, 0x23, 0x12, 0x28, 0x0a, 0x24, 0x43, 0x4f, 0x4e, 0x46, 0x4c,
	0x49, 0x43, 0x54, 0x49, 0x4e, 0x47, 0x5f, 0x43, 0x41, 0x4c, 0x4c, 0x5f, 0x43, 0x4f, 0x4e, 0x56,
	0x45, 0x52, 0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x53, 0x45, 0x54, 0x54, 0x49, 0x4e, 0x47, 0x53, 0x10,
	0x24, 0x12, 0x1b, 0x0a, 0x17, 0x45, 0x58, 0x54, 0x45, 0x4e, 0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x54,
	0x59, 0x50, 0x45, 0x5f, 0x4d, 0x49, 0x53, 0x4d, 0x41, 0x54, 0x43, 0x48, 0x10, 0x25, 0x12, 0x1e,
	0x0a, 0x1a, 0x45, 0x58, 0x54, 0x45, 0x4e, 0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x53, 0x55, 0x42, 0x54,
	0x59, 0x50, 0x45, 0x5f, 0x52, 0x45, 0x51, 0x55, 0x49, 0x52, 0x45, 0x44, 0x10, 0x26, 0x12, 0x1e,
	0x0a, 0x1a, 0x45, 0x58, 0x54, 0x45, 0x4e, 0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x54, 0x59, 0x50, 0x45,
	0x5f, 0x55, 0x4e, 0x53, 0x55, 0x50, 0x50, 0x4f, 0x52, 0x54, 0x45, 0x44, 0x10, 0x27, 0x12, 0x31,
	0x0a, 0x2d, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x4f, 0x50, 0x45, 0x52, 0x41, 0x54, 0x45,
	0x5f, 0x4f, 0x4e, 0x5f, 0x46, 0x45, 0x45, 0x44, 0x5f, 0x57, 0x49, 0x54, 0x48, 0x5f, 0x4d, 0x55,
	0x4c, 0x54, 0x49, 0x50, 0x4c, 0x45, 0x5f, 0x4d, 0x41, 0x50, 0x50, 0x49, 0x4e, 0x47, 0x53, 0x10,
	0x28, 0x12, 0x2e, 0x0a, 0x2a, 0x43, 0x41, 0x4e, 0x4e, 0x4f, 0x54, 0x5f, 0x4f, 0x50, 0x45, 0x52,
	0x41, 0x54, 0x45, 0x5f, 0x4f, 0x4e, 0x5f, 0x46, 0x45, 0x45, 0x44, 0x5f, 0x57, 0x49, 0x54, 0x48,
	0x5f, 0x4b, 0x45, 0x59, 0x5f, 0x41, 0x54, 0x54, 0x52, 0x49, 0x42, 0x55, 0x54, 0x45, 0x53, 0x10,
	0x29, 0x12, 0x18, 0x0a, 0x14, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44, 0x5f, 0x50, 0x52, 0x49,
	0x43, 0x45, 0x5f, 0x46, 0x4f, 0x52, 0x4d, 0x41, 0x54, 0x10, 0x2a, 0x12, 0x1a, 0x0a, 0x16, 0x50,
	0x52, 0x4f, 0x4d, 0x4f, 0x54, 0x49, 0x4f, 0x4e, 0x5f, 0x49, 0x4e, 0x56, 0x41, 0x4c, 0x49, 0x44,
	0x5f, 0x54, 0x49, 0x4d, 0x45, 0x10, 0x2b, 0x12, 0x25, 0x0a, 0x21, 0x54, 0x4f, 0x4f, 0x5f, 0x4d,
	0x41, 0x4e, 0x59, 0x5f, 0x44, 0x45, 0x43, 0x49, 0x4d, 0x41, 0x4c, 0x5f, 0x50, 0x4c, 0x41, 0x43,
	0x45, 0x53, 0x5f, 0x53, 0x50, 0x45, 0x43, 0x49, 0x46, 0x49, 0x45, 0x44, 0x10, 0x2c, 0x12, 0x24,
	0x0a, 0x20, 0x43, 0x4f, 0x4e, 0x43, 0x52, 0x45, 0x54, 0x45, 0x5f, 0x45, 0x58, 0x54, 0x45, 0x4e,
	0x53, 0x49, 0x4f, 0x4e, 0x5f, 0x54, 0x59, 0x50, 0x45, 0x5f, 0x52, 0x45, 0x51, 0x55, 0x49, 0x52,
	0x45, 0x44, 0x10, 0x2d, 0x12, 0x20, 0x0a, 0x1c, 0x53, 0x43, 0x48, 0x45, 0x44, 0x55, 0x4c, 0x45,
	0x5f, 0x45, 0x4e, 0x44, 0x5f, 0x4e, 0x4f, 0x54, 0x5f, 0x41, 0x46, 0x54, 0x45, 0x52, 0x5f, 0x53,
	0x54, 0x41, 0x52, 0x54, 0x10, 0x2e, 0x42, 0xf6, 0x01, 0x0a, 0x22, 0x63, 0x6f, 0x6d, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x61, 0x64, 0x73, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x61, 0x64, 0x73, 0x2e, 0x76, 0x34, 0x2e, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x42, 0x1b, 0x45,
	0x78, 0x74, 0x65, 0x6e, 0x73, 0x69, 0x6f, 0x6e, 0x46, 0x65, 0x65, 0x64, 0x49, 0x74, 0x65, 0x6d,
	0x45, 0x72, 0x72, 0x6f, 0x72, 0x50, 0x72, 0x6f, 0x74, 0x6f, 0x50, 0x01, 0x5a, 0x44, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f,
	0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61,
	0x70, 0x69, 0x73, 0x2f, 0x61, 0x64, 0x73, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x64,
	0x73, 0x2f, 0x76, 0x34, 0x2f, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x3b, 0x65, 0x72, 0x72, 0x6f,
	0x72, 0x73, 0xa2, 0x02, 0x03, 0x47, 0x41, 0x41, 0xaa, 0x02, 0x1e, 0x47, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x2e, 0x41, 0x64, 0x73, 0x2e, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73, 0x2e,
	0x56, 0x34, 0x2e, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x73, 0xca, 0x02, 0x1e, 0x47, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x5c, 0x41, 0x64, 0x73, 0x5c, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x41, 0x64, 0x73,
	0x5c, 0x56, 0x34, 0x5c, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x73, 0xea, 0x02, 0x22, 0x47, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x3a, 0x3a, 0x41, 0x64, 0x73, 0x3a, 0x3a, 0x47, 0x6f, 0x6f, 0x67, 0x6c, 0x65,
	0x41, 0x64, 0x73, 0x3a, 0x3a, 0x56, 0x34, 0x3a, 0x3a, 0x45, 0x72, 0x72, 0x6f, 0x72, 0x73, 0x62,
	0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDescOnce sync.Once
	file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDescData = file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDesc
)

func file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDescGZIP() []byte {
	file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDescOnce.Do(func() {
		file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDescData)
	})
	return file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDescData
}

var file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_enumTypes = make([]protoimpl.EnumInfo, 1)
var file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_msgTypes = make([]protoimpl.MessageInfo, 1)
var file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_goTypes = []interface{}{
	(ExtensionFeedItemErrorEnum_ExtensionFeedItemError)(0), // 0: google.ads.googleads.v4.errors.ExtensionFeedItemErrorEnum.ExtensionFeedItemError
	(*ExtensionFeedItemErrorEnum)(nil),                     // 1: google.ads.googleads.v4.errors.ExtensionFeedItemErrorEnum
}
var file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_depIdxs = []int32{
	0, // [0:0] is the sub-list for method output_type
	0, // [0:0] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() { file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_init() }
func file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_init() {
	if File_google_ads_googleads_v4_errors_extension_feed_item_error_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*ExtensionFeedItemErrorEnum); i {
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
			RawDescriptor: file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDesc,
			NumEnums:      1,
			NumMessages:   1,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_goTypes,
		DependencyIndexes: file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_depIdxs,
		EnumInfos:         file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_enumTypes,
		MessageInfos:      file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_msgTypes,
	}.Build()
	File_google_ads_googleads_v4_errors_extension_feed_item_error_proto = out.File
	file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_rawDesc = nil
	file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_goTypes = nil
	file_google_ads_googleads_v4_errors_extension_feed_item_error_proto_depIdxs = nil
}
