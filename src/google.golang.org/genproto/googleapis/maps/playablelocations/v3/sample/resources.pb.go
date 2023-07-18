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
// source: google/maps/playablelocations/v3/sample/resources.proto

package sample

import (
	reflect "reflect"
	sync "sync"

	proto "github.com/golang/protobuf/proto"
	_ "google.golang.org/genproto/googleapis/api/annotations"
	latlng "google.golang.org/genproto/googleapis/type/latlng"
	field_mask "google.golang.org/genproto/protobuf/field_mask"
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

// Specifies whether the playable location's geographic coordinates (latitude
// and longitude) correspond to its center-point, or to its location snapped
// to the sidewalk of the nearest road.
type SpacingOptions_PointType int32

const (
	// Unspecified point type. Do not use this value.
	SpacingOptions_POINT_TYPE_UNSPECIFIED SpacingOptions_PointType = 0
	// The geographic coordinates correspond to the center of the location.
	SpacingOptions_CENTER_POINT SpacingOptions_PointType = 1
	// The geographic coordinates correspond to the location snapped to the
	// sidewalk of the nearest road (when a nearby road exists).
	SpacingOptions_SNAPPED_POINT SpacingOptions_PointType = 2
)

// Enum value maps for SpacingOptions_PointType.
var (
	SpacingOptions_PointType_name = map[int32]string{
		0: "POINT_TYPE_UNSPECIFIED",
		1: "CENTER_POINT",
		2: "SNAPPED_POINT",
	}
	SpacingOptions_PointType_value = map[string]int32{
		"POINT_TYPE_UNSPECIFIED": 0,
		"CENTER_POINT":           1,
		"SNAPPED_POINT":          2,
	}
)

func (x SpacingOptions_PointType) Enum() *SpacingOptions_PointType {
	p := new(SpacingOptions_PointType)
	*p = x
	return p
}

func (x SpacingOptions_PointType) String() string {
	return protoimpl.X.EnumStringOf(x.Descriptor(), protoreflect.EnumNumber(x))
}

func (SpacingOptions_PointType) Descriptor() protoreflect.EnumDescriptor {
	return file_google_maps_playablelocations_v3_sample_resources_proto_enumTypes[0].Descriptor()
}

func (SpacingOptions_PointType) Type() protoreflect.EnumType {
	return &file_google_maps_playablelocations_v3_sample_resources_proto_enumTypes[0]
}

func (x SpacingOptions_PointType) Number() protoreflect.EnumNumber {
	return protoreflect.EnumNumber(x)
}

// Deprecated: Use SpacingOptions_PointType.Descriptor instead.
func (SpacingOptions_PointType) EnumDescriptor() ([]byte, []int) {
	return file_google_maps_playablelocations_v3_sample_resources_proto_rawDescGZIP(), []int{1, 0}
}

// A geographical point suitable for placing game objects in location-based
// games.
type PlayableLocation struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Required. The name of this playable location.
	Name string `protobuf:"bytes,1,opt,name=name,proto3" json:"name,omitempty"`
	// Required.
	// Each location has one of the following identifiers:
	//
	// Types that are assignable to LocationId:
	//	*PlayableLocation_PlaceId
	//	*PlayableLocation_PlusCode
	LocationId isPlayableLocation_LocationId `protobuf_oneof:"location_id"`
	// A collection of [Playable Location Types](/maps/tt/games/types) for this
	// playable location. The first type in the collection is the primary type.
	//
	// Type information might not be available for all playable locations.
	Types []string `protobuf:"bytes,4,rep,name=types,proto3" json:"types,omitempty"`
	// Required. The latitude and longitude associated with the center of the
	// playable location.
	//
	// By default, the set of playable locations returned from
	// [SamplePlayableLocations][google.maps.playablelocations.v3.PlayableLocations.SamplePlayableLocations]
	// use center-point coordinates.
	CenterPoint *latlng.LatLng `protobuf:"bytes,5,opt,name=center_point,json=centerPoint,proto3" json:"center_point,omitempty"`
	// The playable location's coordinates, snapped to the sidewalk of the
	// nearest road, if a nearby road exists.
	SnappedPoint *latlng.LatLng `protobuf:"bytes,6,opt,name=snapped_point,json=snappedPoint,proto3" json:"snapped_point,omitempty"`
}

func (x *PlayableLocation) Reset() {
	*x = PlayableLocation{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *PlayableLocation) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*PlayableLocation) ProtoMessage() {}

func (x *PlayableLocation) ProtoReflect() protoreflect.Message {
	mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use PlayableLocation.ProtoReflect.Descriptor instead.
func (*PlayableLocation) Descriptor() ([]byte, []int) {
	return file_google_maps_playablelocations_v3_sample_resources_proto_rawDescGZIP(), []int{0}
}

func (x *PlayableLocation) GetName() string {
	if x != nil {
		return x.Name
	}
	return ""
}

func (m *PlayableLocation) GetLocationId() isPlayableLocation_LocationId {
	if m != nil {
		return m.LocationId
	}
	return nil
}

func (x *PlayableLocation) GetPlaceId() string {
	if x, ok := x.GetLocationId().(*PlayableLocation_PlaceId); ok {
		return x.PlaceId
	}
	return ""
}

func (x *PlayableLocation) GetPlusCode() string {
	if x, ok := x.GetLocationId().(*PlayableLocation_PlusCode); ok {
		return x.PlusCode
	}
	return ""
}

func (x *PlayableLocation) GetTypes() []string {
	if x != nil {
		return x.Types
	}
	return nil
}

func (x *PlayableLocation) GetCenterPoint() *latlng.LatLng {
	if x != nil {
		return x.CenterPoint
	}
	return nil
}

func (x *PlayableLocation) GetSnappedPoint() *latlng.LatLng {
	if x != nil {
		return x.SnappedPoint
	}
	return nil
}

type isPlayableLocation_LocationId interface {
	isPlayableLocation_LocationId()
}

type PlayableLocation_PlaceId struct {
	// A [place ID] (https://developers.google.com/places/place-id)
	PlaceId string `protobuf:"bytes,2,opt,name=place_id,json=placeId,proto3,oneof"`
}

type PlayableLocation_PlusCode struct {
	// A [plus code] (http://openlocationcode.com)
	PlusCode string `protobuf:"bytes,3,opt,name=plus_code,json=plusCode,proto3,oneof"`
}

func (*PlayableLocation_PlaceId) isPlayableLocation_LocationId() {}

func (*PlayableLocation_PlusCode) isPlayableLocation_LocationId() {}

// A set of options that specifies the separation between playable locations.
type SpacingOptions struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Required. The minimum spacing between any two playable locations, measured
	// in meters. The minimum value is 30. The maximum value is 1000.
	//
	// Inputs will be rounded up to the next 10 meter interval.
	//
	// The default value is 200m.
	//
	// Set this field to remove tight clusters of playable locations.
	//
	// Note:
	//
	// The spacing is a greedy algorithm. It optimizes for selecting the highest
	// ranking locations first, not to maximize the number of locations selected.
	// Consider the following scenario:
	//
	//   * Rank: A: 2, B: 1, C: 3.
	//   * Distance: A--200m--B--200m--C
	//
	// If spacing=250, it will pick the highest ranked location [B], not [A, C].
	//
	//
	// Note:
	//
	// Spacing works within the game object type itself, as well as the previous
	// ones.
	// Suppose three game object types, each with the following spacing:
	//
	//   * X: 400m, Y: undefined, Z: 200m.
	//
	// 1. Add locations for X, within 400m of each other.
	// 2. Add locations for Y, without any spacing.
	// 3. Finally, add locations for Z within 200m of each other as well X and Y.
	//
	// The distance diagram between those locations end up as:
	//
	//   * From->To.
	//   * X->X: 400m
	//   * Y->X, Y->Y: unspecified.
	//   * Z->X, Z->Y, Z->Z: 200m.
	MinSpacingMeters float64 `protobuf:"fixed64,1,opt,name=min_spacing_meters,json=minSpacingMeters,proto3" json:"min_spacing_meters,omitempty"`
	// Specifies whether the minimum spacing constraint applies to the
	// center-point or to the snapped point of playable locations. The default
	// value is `CENTER_POINT`.
	//
	// If a snapped point is not available for a playable location, its
	// center-point is used instead.
	//
	// Set this to the point type used in your game.
	PointType SpacingOptions_PointType `protobuf:"varint,2,opt,name=point_type,json=pointType,proto3,enum=google.maps.playablelocations.v3.sample.SpacingOptions_PointType" json:"point_type,omitempty"`
}

func (x *SpacingOptions) Reset() {
	*x = SpacingOptions{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *SpacingOptions) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*SpacingOptions) ProtoMessage() {}

func (x *SpacingOptions) ProtoReflect() protoreflect.Message {
	mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use SpacingOptions.ProtoReflect.Descriptor instead.
func (*SpacingOptions) Descriptor() ([]byte, []int) {
	return file_google_maps_playablelocations_v3_sample_resources_proto_rawDescGZIP(), []int{1}
}

func (x *SpacingOptions) GetMinSpacingMeters() float64 {
	if x != nil {
		return x.MinSpacingMeters
	}
	return 0
}

func (x *SpacingOptions) GetPointType() SpacingOptions_PointType {
	if x != nil {
		return x.PointType
	}
	return SpacingOptions_POINT_TYPE_UNSPECIFIED
}

// Specifies the filters to use when searching for playable locations.
type Filter struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Specifies the maximum number of playable locations to return. This value
	// must not be greater than 1000. The default value is 100.
	//
	// Only the top-ranking playable locations are returned.
	MaxLocationCount int32 `protobuf:"varint,1,opt,name=max_location_count,json=maxLocationCount,proto3" json:"max_location_count,omitempty"`
	// A set of options that control the spacing between playable locations. By
	// default the minimum distance between locations is 200m.
	Spacing *SpacingOptions `protobuf:"bytes,2,opt,name=spacing,proto3" json:"spacing,omitempty"`
	// Restricts the set of playable locations to just the
	// [types](/maps/tt/games/types) that you want.
	IncludedTypes []string `protobuf:"bytes,3,rep,name=included_types,json=includedTypes,proto3" json:"included_types,omitempty"`
}

func (x *Filter) Reset() {
	*x = Filter{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[2]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *Filter) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*Filter) ProtoMessage() {}

func (x *Filter) ProtoReflect() protoreflect.Message {
	mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[2]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use Filter.ProtoReflect.Descriptor instead.
func (*Filter) Descriptor() ([]byte, []int) {
	return file_google_maps_playablelocations_v3_sample_resources_proto_rawDescGZIP(), []int{2}
}

func (x *Filter) GetMaxLocationCount() int32 {
	if x != nil {
		return x.MaxLocationCount
	}
	return 0
}

func (x *Filter) GetSpacing() *SpacingOptions {
	if x != nil {
		return x.Spacing
	}
	return nil
}

func (x *Filter) GetIncludedTypes() []string {
	if x != nil {
		return x.IncludedTypes
	}
	return nil
}

// Encapsulates a filter criterion for searching for a set of playable
// locations.
type Criterion struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Required. An arbitrary, developer-defined identifier of the type of game
	// object that the playable location is used for. This field allows you to
	// specify criteria per game object type when searching for playable
	// locations.
	//
	// You should assign a unique `game_object_type` ID across all
	// `request_criteria` to represent a distinct type of game object. For
	// example, 1=monster location, 2=powerup location.
	//
	// The response contains a map<game_object_type, Response>.
	GameObjectType int32 `protobuf:"varint,1,opt,name=game_object_type,json=gameObjectType,proto3" json:"game_object_type,omitempty"`
	// Specifies filtering options, and specifies what will be included in the
	// result set.
	Filter *Filter `protobuf:"bytes,2,opt,name=filter,proto3" json:"filter,omitempty"`
	// Specifies which `PlayableLocation` fields are returned.
	//
	// `name` (which is used for logging impressions), `center_point` and
	// `place_id` (or `plus_code`) are always returned.
	//
	// The following fields are omitted unless you specify them here:
	//
	//   * snapped_point
	//   * types
	//
	// Note: The more fields you include, the more expensive in terms of data and
	// associated latency your query will be.
	FieldsToReturn *field_mask.FieldMask `protobuf:"bytes,3,opt,name=fields_to_return,json=fieldsToReturn,proto3" json:"fields_to_return,omitempty"`
}

func (x *Criterion) Reset() {
	*x = Criterion{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[3]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *Criterion) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*Criterion) ProtoMessage() {}

func (x *Criterion) ProtoReflect() protoreflect.Message {
	mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[3]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use Criterion.ProtoReflect.Descriptor instead.
func (*Criterion) Descriptor() ([]byte, []int) {
	return file_google_maps_playablelocations_v3_sample_resources_proto_rawDescGZIP(), []int{3}
}

func (x *Criterion) GetGameObjectType() int32 {
	if x != nil {
		return x.GameObjectType
	}
	return 0
}

func (x *Criterion) GetFilter() *Filter {
	if x != nil {
		return x.Filter
	}
	return nil
}

func (x *Criterion) GetFieldsToReturn() *field_mask.FieldMask {
	if x != nil {
		return x.FieldsToReturn
	}
	return nil
}

// Specifies the area to search for playable locations.
type AreaFilter struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// Required. The S2 cell ID of the area you want. This must be between cell
	// level 11 and 14 (inclusive).
	//
	// S2 cells are 64-bit integers that identify areas on the Earth. They are
	// hierarchical, and can therefore be used for spatial indexing.
	//
	// The S2 geometry library is available in a number of languages:
	//
	//   * [C++](https://github.com/google/s2geometry)
	//   * [Java](https://github.com/google/s2-geometry-library-java)
	//   * [Go](https://github.com/golang/geo)
	//   * [Python](https://github.com/google/s2geometry/tree/master/src/python)
	S2CellId uint64 `protobuf:"fixed64,1,opt,name=s2_cell_id,json=s2CellId,proto3" json:"s2_cell_id,omitempty"`
}

func (x *AreaFilter) Reset() {
	*x = AreaFilter{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[4]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *AreaFilter) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*AreaFilter) ProtoMessage() {}

func (x *AreaFilter) ProtoReflect() protoreflect.Message {
	mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[4]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use AreaFilter.ProtoReflect.Descriptor instead.
func (*AreaFilter) Descriptor() ([]byte, []int) {
	return file_google_maps_playablelocations_v3_sample_resources_proto_rawDescGZIP(), []int{4}
}

func (x *AreaFilter) GetS2CellId() uint64 {
	if x != nil {
		return x.S2CellId
	}
	return 0
}

// A list of PlayableLocation objects that satisfies a single Criterion.
type PlayableLocationList struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// A list of playable locations for this game object type.
	Locations []*PlayableLocation `protobuf:"bytes,1,rep,name=locations,proto3" json:"locations,omitempty"`
}

func (x *PlayableLocationList) Reset() {
	*x = PlayableLocationList{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[5]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *PlayableLocationList) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*PlayableLocationList) ProtoMessage() {}

func (x *PlayableLocationList) ProtoReflect() protoreflect.Message {
	mi := &file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[5]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use PlayableLocationList.ProtoReflect.Descriptor instead.
func (*PlayableLocationList) Descriptor() ([]byte, []int) {
	return file_google_maps_playablelocations_v3_sample_resources_proto_rawDescGZIP(), []int{5}
}

func (x *PlayableLocationList) GetLocations() []*PlayableLocation {
	if x != nil {
		return x.Locations
	}
	return nil
}

var File_google_maps_playablelocations_v3_sample_resources_proto protoreflect.FileDescriptor

var file_google_maps_playablelocations_v3_sample_resources_proto_rawDesc = []byte{
	0x0a, 0x37, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x6d, 0x61, 0x70, 0x73, 0x2f, 0x70, 0x6c,
	0x61, 0x79, 0x61, 0x62, 0x6c, 0x65, 0x6c, 0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2f,
	0x76, 0x33, 0x2f, 0x73, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2f, 0x72, 0x65, 0x73, 0x6f, 0x75, 0x72,
	0x63, 0x65, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x27, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x2e, 0x6d, 0x61, 0x70, 0x73, 0x2e, 0x70, 0x6c, 0x61, 0x79, 0x61, 0x62, 0x6c, 0x65, 0x6c,
	0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x76, 0x33, 0x2e, 0x73, 0x61, 0x6d, 0x70,
	0x6c, 0x65, 0x1a, 0x1f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x66,
	0x69, 0x65, 0x6c, 0x64, 0x5f, 0x62, 0x65, 0x68, 0x61, 0x76, 0x69, 0x6f, 0x72, 0x2e, 0x70, 0x72,
	0x6f, 0x74, 0x6f, 0x1a, 0x20, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x70, 0x72, 0x6f, 0x74,
	0x6f, 0x62, 0x75, 0x66, 0x2f, 0x66, 0x69, 0x65, 0x6c, 0x64, 0x5f, 0x6d, 0x61, 0x73, 0x6b, 0x2e,
	0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x18, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x74, 0x79,
	0x70, 0x65, 0x2f, 0x6c, 0x61, 0x74, 0x6c, 0x6e, 0x67, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22,
	0xf9, 0x01, 0x0a, 0x10, 0x50, 0x6c, 0x61, 0x79, 0x61, 0x62, 0x6c, 0x65, 0x4c, 0x6f, 0x63, 0x61,
	0x74, 0x69, 0x6f, 0x6e, 0x12, 0x12, 0x0a, 0x04, 0x6e, 0x61, 0x6d, 0x65, 0x18, 0x01, 0x20, 0x01,
	0x28, 0x09, 0x52, 0x04, 0x6e, 0x61, 0x6d, 0x65, 0x12, 0x1b, 0x0a, 0x08, 0x70, 0x6c, 0x61, 0x63,
	0x65, 0x5f, 0x69, 0x64, 0x18, 0x02, 0x20, 0x01, 0x28, 0x09, 0x48, 0x00, 0x52, 0x07, 0x70, 0x6c,
	0x61, 0x63, 0x65, 0x49, 0x64, 0x12, 0x1d, 0x0a, 0x09, 0x70, 0x6c, 0x75, 0x73, 0x5f, 0x63, 0x6f,
	0x64, 0x65, 0x18, 0x03, 0x20, 0x01, 0x28, 0x09, 0x48, 0x00, 0x52, 0x08, 0x70, 0x6c, 0x75, 0x73,
	0x43, 0x6f, 0x64, 0x65, 0x12, 0x14, 0x0a, 0x05, 0x74, 0x79, 0x70, 0x65, 0x73, 0x18, 0x04, 0x20,
	0x03, 0x28, 0x09, 0x52, 0x05, 0x74, 0x79, 0x70, 0x65, 0x73, 0x12, 0x36, 0x0a, 0x0c, 0x63, 0x65,
	0x6e, 0x74, 0x65, 0x72, 0x5f, 0x70, 0x6f, 0x69, 0x6e, 0x74, 0x18, 0x05, 0x20, 0x01, 0x28, 0x0b,
	0x32, 0x13, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x74, 0x79, 0x70, 0x65, 0x2e, 0x4c,
	0x61, 0x74, 0x4c, 0x6e, 0x67, 0x52, 0x0b, 0x63, 0x65, 0x6e, 0x74, 0x65, 0x72, 0x50, 0x6f, 0x69,
	0x6e, 0x74, 0x12, 0x38, 0x0a, 0x0d, 0x73, 0x6e, 0x61, 0x70, 0x70, 0x65, 0x64, 0x5f, 0x70, 0x6f,
	0x69, 0x6e, 0x74, 0x18, 0x06, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x13, 0x2e, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x2e, 0x74, 0x79, 0x70, 0x65, 0x2e, 0x4c, 0x61, 0x74, 0x4c, 0x6e, 0x67, 0x52, 0x0c,
	0x73, 0x6e, 0x61, 0x70, 0x70, 0x65, 0x64, 0x50, 0x6f, 0x69, 0x6e, 0x74, 0x42, 0x0d, 0x0a, 0x0b,
	0x6c, 0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x5f, 0x69, 0x64, 0x22, 0xf3, 0x01, 0x0a, 0x0e,
	0x53, 0x70, 0x61, 0x63, 0x69, 0x6e, 0x67, 0x4f, 0x70, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x12, 0x31,
	0x0a, 0x12, 0x6d, 0x69, 0x6e, 0x5f, 0x73, 0x70, 0x61, 0x63, 0x69, 0x6e, 0x67, 0x5f, 0x6d, 0x65,
	0x74, 0x65, 0x72, 0x73, 0x18, 0x01, 0x20, 0x01, 0x28, 0x01, 0x42, 0x03, 0xe0, 0x41, 0x02, 0x52,
	0x10, 0x6d, 0x69, 0x6e, 0x53, 0x70, 0x61, 0x63, 0x69, 0x6e, 0x67, 0x4d, 0x65, 0x74, 0x65, 0x72,
	0x73, 0x12, 0x60, 0x0a, 0x0a, 0x70, 0x6f, 0x69, 0x6e, 0x74, 0x5f, 0x74, 0x79, 0x70, 0x65, 0x18,
	0x02, 0x20, 0x01, 0x28, 0x0e, 0x32, 0x41, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x6d,
	0x61, 0x70, 0x73, 0x2e, 0x70, 0x6c, 0x61, 0x79, 0x61, 0x62, 0x6c, 0x65, 0x6c, 0x6f, 0x63, 0x61,
	0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x76, 0x33, 0x2e, 0x73, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e,
	0x53, 0x70, 0x61, 0x63, 0x69, 0x6e, 0x67, 0x4f, 0x70, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x50,
	0x6f, 0x69, 0x6e, 0x74, 0x54, 0x79, 0x70, 0x65, 0x52, 0x09, 0x70, 0x6f, 0x69, 0x6e, 0x74, 0x54,
	0x79, 0x70, 0x65, 0x22, 0x4c, 0x0a, 0x09, 0x50, 0x6f, 0x69, 0x6e, 0x74, 0x54, 0x79, 0x70, 0x65,
	0x12, 0x1a, 0x0a, 0x16, 0x50, 0x4f, 0x49, 0x4e, 0x54, 0x5f, 0x54, 0x59, 0x50, 0x45, 0x5f, 0x55,
	0x4e, 0x53, 0x50, 0x45, 0x43, 0x49, 0x46, 0x49, 0x45, 0x44, 0x10, 0x00, 0x12, 0x10, 0x0a, 0x0c,
	0x43, 0x45, 0x4e, 0x54, 0x45, 0x52, 0x5f, 0x50, 0x4f, 0x49, 0x4e, 0x54, 0x10, 0x01, 0x12, 0x11,
	0x0a, 0x0d, 0x53, 0x4e, 0x41, 0x50, 0x50, 0x45, 0x44, 0x5f, 0x50, 0x4f, 0x49, 0x4e, 0x54, 0x10,
	0x02, 0x22, 0xb0, 0x01, 0x0a, 0x06, 0x46, 0x69, 0x6c, 0x74, 0x65, 0x72, 0x12, 0x2c, 0x0a, 0x12,
	0x6d, 0x61, 0x78, 0x5f, 0x6c, 0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x5f, 0x63, 0x6f, 0x75,
	0x6e, 0x74, 0x18, 0x01, 0x20, 0x01, 0x28, 0x05, 0x52, 0x10, 0x6d, 0x61, 0x78, 0x4c, 0x6f, 0x63,
	0x61, 0x74, 0x69, 0x6f, 0x6e, 0x43, 0x6f, 0x75, 0x6e, 0x74, 0x12, 0x51, 0x0a, 0x07, 0x73, 0x70,
	0x61, 0x63, 0x69, 0x6e, 0x67, 0x18, 0x02, 0x20, 0x01, 0x28, 0x0b, 0x32, 0x37, 0x2e, 0x67, 0x6f,
	0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x6d, 0x61, 0x70, 0x73, 0x2e, 0x70, 0x6c, 0x61, 0x79, 0x61, 0x62,
	0x6c, 0x65, 0x6c, 0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x76, 0x33, 0x2e, 0x73,
	0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x53, 0x70, 0x61, 0x63, 0x69, 0x6e, 0x67, 0x4f, 0x70, 0x74,
	0x69, 0x6f, 0x6e, 0x73, 0x52, 0x07, 0x73, 0x70, 0x61, 0x63, 0x69, 0x6e, 0x67, 0x12, 0x25, 0x0a,
	0x0e, 0x69, 0x6e, 0x63, 0x6c, 0x75, 0x64, 0x65, 0x64, 0x5f, 0x74, 0x79, 0x70, 0x65, 0x73, 0x18,
	0x03, 0x20, 0x03, 0x28, 0x09, 0x52, 0x0d, 0x69, 0x6e, 0x63, 0x6c, 0x75, 0x64, 0x65, 0x64, 0x54,
	0x79, 0x70, 0x65, 0x73, 0x22, 0xc9, 0x01, 0x0a, 0x09, 0x43, 0x72, 0x69, 0x74, 0x65, 0x72, 0x69,
	0x6f, 0x6e, 0x12, 0x2d, 0x0a, 0x10, 0x67, 0x61, 0x6d, 0x65, 0x5f, 0x6f, 0x62, 0x6a, 0x65, 0x63,
	0x74, 0x5f, 0x74, 0x79, 0x70, 0x65, 0x18, 0x01, 0x20, 0x01, 0x28, 0x05, 0x42, 0x03, 0xe0, 0x41,
	0x02, 0x52, 0x0e, 0x67, 0x61, 0x6d, 0x65, 0x4f, 0x62, 0x6a, 0x65, 0x63, 0x74, 0x54, 0x79, 0x70,
	0x65, 0x12, 0x47, 0x0a, 0x06, 0x66, 0x69, 0x6c, 0x74, 0x65, 0x72, 0x18, 0x02, 0x20, 0x01, 0x28,
	0x0b, 0x32, 0x2f, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x6d, 0x61, 0x70, 0x73, 0x2e,
	0x70, 0x6c, 0x61, 0x79, 0x61, 0x62, 0x6c, 0x65, 0x6c, 0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e,
	0x73, 0x2e, 0x76, 0x33, 0x2e, 0x73, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x46, 0x69, 0x6c, 0x74,
	0x65, 0x72, 0x52, 0x06, 0x66, 0x69, 0x6c, 0x74, 0x65, 0x72, 0x12, 0x44, 0x0a, 0x10, 0x66, 0x69,
	0x65, 0x6c, 0x64, 0x73, 0x5f, 0x74, 0x6f, 0x5f, 0x72, 0x65, 0x74, 0x75, 0x72, 0x6e, 0x18, 0x03,
	0x20, 0x01, 0x28, 0x0b, 0x32, 0x1a, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x70, 0x72,
	0x6f, 0x74, 0x6f, 0x62, 0x75, 0x66, 0x2e, 0x46, 0x69, 0x65, 0x6c, 0x64, 0x4d, 0x61, 0x73, 0x6b,
	0x52, 0x0e, 0x66, 0x69, 0x65, 0x6c, 0x64, 0x73, 0x54, 0x6f, 0x52, 0x65, 0x74, 0x75, 0x72, 0x6e,
	0x22, 0x2f, 0x0a, 0x0a, 0x41, 0x72, 0x65, 0x61, 0x46, 0x69, 0x6c, 0x74, 0x65, 0x72, 0x12, 0x21,
	0x0a, 0x0a, 0x73, 0x32, 0x5f, 0x63, 0x65, 0x6c, 0x6c, 0x5f, 0x69, 0x64, 0x18, 0x01, 0x20, 0x01,
	0x28, 0x06, 0x42, 0x03, 0xe0, 0x41, 0x02, 0x52, 0x08, 0x73, 0x32, 0x43, 0x65, 0x6c, 0x6c, 0x49,
	0x64, 0x22, 0x6f, 0x0a, 0x14, 0x50, 0x6c, 0x61, 0x79, 0x61, 0x62, 0x6c, 0x65, 0x4c, 0x6f, 0x63,
	0x61, 0x74, 0x69, 0x6f, 0x6e, 0x4c, 0x69, 0x73, 0x74, 0x12, 0x57, 0x0a, 0x09, 0x6c, 0x6f, 0x63,
	0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x18, 0x01, 0x20, 0x03, 0x28, 0x0b, 0x32, 0x39, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x6d, 0x61, 0x70, 0x73, 0x2e, 0x70, 0x6c, 0x61, 0x79, 0x61,
	0x62, 0x6c, 0x65, 0x6c, 0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x76, 0x33, 0x2e,
	0x73, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x50, 0x6c, 0x61, 0x79, 0x61, 0x62, 0x6c, 0x65, 0x4c,
	0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x52, 0x09, 0x6c, 0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f,
	0x6e, 0x73, 0x42, 0xbf, 0x01, 0x0a, 0x2b, 0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c,
	0x65, 0x2e, 0x6d, 0x61, 0x70, 0x73, 0x2e, 0x70, 0x6c, 0x61, 0x79, 0x61, 0x62, 0x6c, 0x65, 0x6c,
	0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x76, 0x33, 0x2e, 0x73, 0x61, 0x6d, 0x70,
	0x6c, 0x65, 0x42, 0x0e, 0x52, 0x65, 0x73, 0x6f, 0x75, 0x72, 0x63, 0x65, 0x73, 0x50, 0x72, 0x6f,
	0x74, 0x6f, 0x50, 0x01, 0x5a, 0x4d, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67, 0x6f, 0x6c,
	0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f, 0x74, 0x6f,
	0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x6d, 0x61, 0x70, 0x73,
	0x2f, 0x70, 0x6c, 0x61, 0x79, 0x61, 0x62, 0x6c, 0x65, 0x6c, 0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f,
	0x6e, 0x73, 0x2f, 0x76, 0x33, 0x2f, 0x73, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x3b, 0x73, 0x61, 0x6d,
	0x70, 0x6c, 0x65, 0xa2, 0x02, 0x04, 0x47, 0x4d, 0x50, 0x4c, 0xaa, 0x02, 0x27, 0x47, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x2e, 0x4d, 0x61, 0x70, 0x73, 0x2e, 0x50, 0x6c, 0x61, 0x79, 0x61, 0x62, 0x6c,
	0x65, 0x4c, 0x6f, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x56, 0x33, 0x2e, 0x53, 0x61,
	0x6d, 0x70, 0x6c, 0x65, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_maps_playablelocations_v3_sample_resources_proto_rawDescOnce sync.Once
	file_google_maps_playablelocations_v3_sample_resources_proto_rawDescData = file_google_maps_playablelocations_v3_sample_resources_proto_rawDesc
)

func file_google_maps_playablelocations_v3_sample_resources_proto_rawDescGZIP() []byte {
	file_google_maps_playablelocations_v3_sample_resources_proto_rawDescOnce.Do(func() {
		file_google_maps_playablelocations_v3_sample_resources_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_maps_playablelocations_v3_sample_resources_proto_rawDescData)
	})
	return file_google_maps_playablelocations_v3_sample_resources_proto_rawDescData
}

var file_google_maps_playablelocations_v3_sample_resources_proto_enumTypes = make([]protoimpl.EnumInfo, 1)
var file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes = make([]protoimpl.MessageInfo, 6)
var file_google_maps_playablelocations_v3_sample_resources_proto_goTypes = []interface{}{
	(SpacingOptions_PointType)(0), // 0: google.maps.playablelocations.v3.sample.SpacingOptions.PointType
	(*PlayableLocation)(nil),      // 1: google.maps.playablelocations.v3.sample.PlayableLocation
	(*SpacingOptions)(nil),        // 2: google.maps.playablelocations.v3.sample.SpacingOptions
	(*Filter)(nil),                // 3: google.maps.playablelocations.v3.sample.Filter
	(*Criterion)(nil),             // 4: google.maps.playablelocations.v3.sample.Criterion
	(*AreaFilter)(nil),            // 5: google.maps.playablelocations.v3.sample.AreaFilter
	(*PlayableLocationList)(nil),  // 6: google.maps.playablelocations.v3.sample.PlayableLocationList
	(*latlng.LatLng)(nil),         // 7: google.type.LatLng
	(*field_mask.FieldMask)(nil),  // 8: google.protobuf.FieldMask
}
var file_google_maps_playablelocations_v3_sample_resources_proto_depIdxs = []int32{
	7, // 0: google.maps.playablelocations.v3.sample.PlayableLocation.center_point:type_name -> google.type.LatLng
	7, // 1: google.maps.playablelocations.v3.sample.PlayableLocation.snapped_point:type_name -> google.type.LatLng
	0, // 2: google.maps.playablelocations.v3.sample.SpacingOptions.point_type:type_name -> google.maps.playablelocations.v3.sample.SpacingOptions.PointType
	2, // 3: google.maps.playablelocations.v3.sample.Filter.spacing:type_name -> google.maps.playablelocations.v3.sample.SpacingOptions
	3, // 4: google.maps.playablelocations.v3.sample.Criterion.filter:type_name -> google.maps.playablelocations.v3.sample.Filter
	8, // 5: google.maps.playablelocations.v3.sample.Criterion.fields_to_return:type_name -> google.protobuf.FieldMask
	1, // 6: google.maps.playablelocations.v3.sample.PlayableLocationList.locations:type_name -> google.maps.playablelocations.v3.sample.PlayableLocation
	7, // [7:7] is the sub-list for method output_type
	7, // [7:7] is the sub-list for method input_type
	7, // [7:7] is the sub-list for extension type_name
	7, // [7:7] is the sub-list for extension extendee
	0, // [0:7] is the sub-list for field type_name
}

func init() { file_google_maps_playablelocations_v3_sample_resources_proto_init() }
func file_google_maps_playablelocations_v3_sample_resources_proto_init() {
	if File_google_maps_playablelocations_v3_sample_resources_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*PlayableLocation); i {
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
		file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*SpacingOptions); i {
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
		file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[2].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*Filter); i {
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
		file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[3].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*Criterion); i {
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
		file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[4].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*AreaFilter); i {
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
		file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[5].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*PlayableLocationList); i {
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
	file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes[0].OneofWrappers = []interface{}{
		(*PlayableLocation_PlaceId)(nil),
		(*PlayableLocation_PlusCode)(nil),
	}
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: file_google_maps_playablelocations_v3_sample_resources_proto_rawDesc,
			NumEnums:      1,
			NumMessages:   6,
			NumExtensions: 0,
			NumServices:   0,
		},
		GoTypes:           file_google_maps_playablelocations_v3_sample_resources_proto_goTypes,
		DependencyIndexes: file_google_maps_playablelocations_v3_sample_resources_proto_depIdxs,
		EnumInfos:         file_google_maps_playablelocations_v3_sample_resources_proto_enumTypes,
		MessageInfos:      file_google_maps_playablelocations_v3_sample_resources_proto_msgTypes,
	}.Build()
	File_google_maps_playablelocations_v3_sample_resources_proto = out.File
	file_google_maps_playablelocations_v3_sample_resources_proto_rawDesc = nil
	file_google_maps_playablelocations_v3_sample_resources_proto_goTypes = nil
	file_google_maps_playablelocations_v3_sample_resources_proto_depIdxs = nil
}
