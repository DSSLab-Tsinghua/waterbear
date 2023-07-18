// Copyright 2019 Google LLC.
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
//

// Code generated by protoc-gen-go. DO NOT EDIT.
// versions:
// 	protoc-gen-go v1.22.0
// 	protoc        v3.12.3
// source: google/devtools/resultstore/v2/resultstore_file_download.proto

package resultstore

import (
	context "context"
	reflect "reflect"
	sync "sync"

	proto "github.com/golang/protobuf/proto"
	_ "google.golang.org/genproto/googleapis/api/annotations"
	grpc "google.golang.org/grpc"
	codes "google.golang.org/grpc/codes"
	status "google.golang.org/grpc/status"
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

// Request object for GetFile
type GetFileRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// This corresponds to the uri field in the File message.
	Uri string `protobuf:"bytes,1,opt,name=uri,proto3" json:"uri,omitempty"`
	// The offset for the first byte to return in the read, relative to the start
	// of the resource.
	//
	// A `read_offset` that is negative or greater than the size of the resource
	// will cause an `OUT_OF_RANGE` error.
	ReadOffset int64 `protobuf:"varint,2,opt,name=read_offset,json=readOffset,proto3" json:"read_offset,omitempty"`
	// The maximum number of `data` bytes the server is allowed to return in the
	// sum of all `ReadResponse` messages. A `read_limit` of zero indicates that
	// there is no limit, and a negative `read_limit` will cause an error.
	//
	// If the stream returns fewer bytes than allowed by the `read_limit` and no
	// error occurred, the stream includes all data from the `read_offset` to the
	// end of the resource.
	ReadLimit int64 `protobuf:"varint,3,opt,name=read_limit,json=readLimit,proto3" json:"read_limit,omitempty"`
	// Only applies if the referenced file is a known archive type (ar, jar, zip)
	// The above read_offset and read_limit fields are applied to this entry.
	// If this file is not an archive, INVALID_ARGUMENT is thrown.
	ArchiveEntry string `protobuf:"bytes,4,opt,name=archive_entry,json=archiveEntry,proto3" json:"archive_entry,omitempty"`
}

func (x *GetFileRequest) Reset() {
	*x = GetFileRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *GetFileRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*GetFileRequest) ProtoMessage() {}

func (x *GetFileRequest) ProtoReflect() protoreflect.Message {
	mi := &file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use GetFileRequest.ProtoReflect.Descriptor instead.
func (*GetFileRequest) Descriptor() ([]byte, []int) {
	return file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDescGZIP(), []int{0}
}

func (x *GetFileRequest) GetUri() string {
	if x != nil {
		return x.Uri
	}
	return ""
}

func (x *GetFileRequest) GetReadOffset() int64 {
	if x != nil {
		return x.ReadOffset
	}
	return 0
}

func (x *GetFileRequest) GetReadLimit() int64 {
	if x != nil {
		return x.ReadLimit
	}
	return 0
}

func (x *GetFileRequest) GetArchiveEntry() string {
	if x != nil {
		return x.ArchiveEntry
	}
	return ""
}

// Response object for GetFile
type GetFileResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// The file data.
	Data []byte `protobuf:"bytes,1,opt,name=data,proto3" json:"data,omitempty"`
}

func (x *GetFileResponse) Reset() {
	*x = GetFileResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *GetFileResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*GetFileResponse) ProtoMessage() {}

func (x *GetFileResponse) ProtoReflect() protoreflect.Message {
	mi := &file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use GetFileResponse.ProtoReflect.Descriptor instead.
func (*GetFileResponse) Descriptor() ([]byte, []int) {
	return file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDescGZIP(), []int{1}
}

func (x *GetFileResponse) GetData() []byte {
	if x != nil {
		return x.Data
	}
	return nil
}

// Request object for GetFileTail
type GetFileTailRequest struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// This corresponds to the uri field in the File message.
	Uri string `protobuf:"bytes,1,opt,name=uri,proto3" json:"uri,omitempty"`
	// The offset for the first byte to return in the read, relative to the end
	// of the resource.
	//
	// A `read_offset` that is negative or greater than the size of the resource
	// will cause an `OUT_OF_RANGE` error.
	ReadOffset int64 `protobuf:"varint,2,opt,name=read_offset,json=readOffset,proto3" json:"read_offset,omitempty"`
	// The maximum number of `data` bytes the server is allowed to return. The
	// server will return bytes starting from the tail of the file.
	//
	// A `read_limit` of zero indicates that there is no limit, and a negative
	// `read_limit` will cause an error.
	ReadLimit int64 `protobuf:"varint,3,opt,name=read_limit,json=readLimit,proto3" json:"read_limit,omitempty"`
	// Only applies if the referenced file is a known archive type (ar, jar, zip)
	// The above read_offset and read_limit fields are applied to this entry.
	// If this file is not an archive, INVALID_ARGUMENT is thrown.
	ArchiveEntry string `protobuf:"bytes,4,opt,name=archive_entry,json=archiveEntry,proto3" json:"archive_entry,omitempty"`
}

func (x *GetFileTailRequest) Reset() {
	*x = GetFileTailRequest{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[2]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *GetFileTailRequest) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*GetFileTailRequest) ProtoMessage() {}

func (x *GetFileTailRequest) ProtoReflect() protoreflect.Message {
	mi := &file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[2]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use GetFileTailRequest.ProtoReflect.Descriptor instead.
func (*GetFileTailRequest) Descriptor() ([]byte, []int) {
	return file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDescGZIP(), []int{2}
}

func (x *GetFileTailRequest) GetUri() string {
	if x != nil {
		return x.Uri
	}
	return ""
}

func (x *GetFileTailRequest) GetReadOffset() int64 {
	if x != nil {
		return x.ReadOffset
	}
	return 0
}

func (x *GetFileTailRequest) GetReadLimit() int64 {
	if x != nil {
		return x.ReadLimit
	}
	return 0
}

func (x *GetFileTailRequest) GetArchiveEntry() string {
	if x != nil {
		return x.ArchiveEntry
	}
	return ""
}

// Response object for GetFileTail
type GetFileTailResponse struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// The file data, encoded with UTF-8.
	Data []byte `protobuf:"bytes,1,opt,name=data,proto3" json:"data,omitempty"`
}

func (x *GetFileTailResponse) Reset() {
	*x = GetFileTailResponse{}
	if protoimpl.UnsafeEnabled {
		mi := &file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[3]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *GetFileTailResponse) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*GetFileTailResponse) ProtoMessage() {}

func (x *GetFileTailResponse) ProtoReflect() protoreflect.Message {
	mi := &file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[3]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use GetFileTailResponse.ProtoReflect.Descriptor instead.
func (*GetFileTailResponse) Descriptor() ([]byte, []int) {
	return file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDescGZIP(), []int{3}
}

func (x *GetFileTailResponse) GetData() []byte {
	if x != nil {
		return x.Data
	}
	return nil
}

var File_google_devtools_resultstore_v2_resultstore_file_download_proto protoreflect.FileDescriptor

var file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDesc = []byte{
	0x0a, 0x3e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x64, 0x65, 0x76, 0x74, 0x6f, 0x6f, 0x6c,
	0x73, 0x2f, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73, 0x74, 0x6f, 0x72, 0x65, 0x2f, 0x76, 0x32,
	0x2f, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73, 0x74, 0x6f, 0x72, 0x65, 0x5f, 0x66, 0x69, 0x6c,
	0x65, 0x5f, 0x64, 0x6f, 0x77, 0x6e, 0x6c, 0x6f, 0x61, 0x64, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f,
	0x12, 0x1e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x64, 0x65, 0x76, 0x74, 0x6f, 0x6f, 0x6c,
	0x73, 0x2e, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73, 0x74, 0x6f, 0x72, 0x65, 0x2e, 0x76, 0x32,
	0x1a, 0x1c, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x61, 0x6e, 0x6e,
	0x6f, 0x74, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x73, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x1a, 0x17,
	0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x61, 0x70, 0x69, 0x2f, 0x63, 0x6c, 0x69, 0x65, 0x6e,
	0x74, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22, 0x87, 0x01, 0x0a, 0x0e, 0x47, 0x65, 0x74, 0x46,
	0x69, 0x6c, 0x65, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x12, 0x10, 0x0a, 0x03, 0x75, 0x72,
	0x69, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x03, 0x75, 0x72, 0x69, 0x12, 0x1f, 0x0a, 0x0b,
	0x72, 0x65, 0x61, 0x64, 0x5f, 0x6f, 0x66, 0x66, 0x73, 0x65, 0x74, 0x18, 0x02, 0x20, 0x01, 0x28,
	0x03, 0x52, 0x0a, 0x72, 0x65, 0x61, 0x64, 0x4f, 0x66, 0x66, 0x73, 0x65, 0x74, 0x12, 0x1d, 0x0a,
	0x0a, 0x72, 0x65, 0x61, 0x64, 0x5f, 0x6c, 0x69, 0x6d, 0x69, 0x74, 0x18, 0x03, 0x20, 0x01, 0x28,
	0x03, 0x52, 0x09, 0x72, 0x65, 0x61, 0x64, 0x4c, 0x69, 0x6d, 0x69, 0x74, 0x12, 0x23, 0x0a, 0x0d,
	0x61, 0x72, 0x63, 0x68, 0x69, 0x76, 0x65, 0x5f, 0x65, 0x6e, 0x74, 0x72, 0x79, 0x18, 0x04, 0x20,
	0x01, 0x28, 0x09, 0x52, 0x0c, 0x61, 0x72, 0x63, 0x68, 0x69, 0x76, 0x65, 0x45, 0x6e, 0x74, 0x72,
	0x79, 0x22, 0x25, 0x0a, 0x0f, 0x47, 0x65, 0x74, 0x46, 0x69, 0x6c, 0x65, 0x52, 0x65, 0x73, 0x70,
	0x6f, 0x6e, 0x73, 0x65, 0x12, 0x12, 0x0a, 0x04, 0x64, 0x61, 0x74, 0x61, 0x18, 0x01, 0x20, 0x01,
	0x28, 0x0c, 0x52, 0x04, 0x64, 0x61, 0x74, 0x61, 0x22, 0x8b, 0x01, 0x0a, 0x12, 0x47, 0x65, 0x74,
	0x46, 0x69, 0x6c, 0x65, 0x54, 0x61, 0x69, 0x6c, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x12,
	0x10, 0x0a, 0x03, 0x75, 0x72, 0x69, 0x18, 0x01, 0x20, 0x01, 0x28, 0x09, 0x52, 0x03, 0x75, 0x72,
	0x69, 0x12, 0x1f, 0x0a, 0x0b, 0x72, 0x65, 0x61, 0x64, 0x5f, 0x6f, 0x66, 0x66, 0x73, 0x65, 0x74,
	0x18, 0x02, 0x20, 0x01, 0x28, 0x03, 0x52, 0x0a, 0x72, 0x65, 0x61, 0x64, 0x4f, 0x66, 0x66, 0x73,
	0x65, 0x74, 0x12, 0x1d, 0x0a, 0x0a, 0x72, 0x65, 0x61, 0x64, 0x5f, 0x6c, 0x69, 0x6d, 0x69, 0x74,
	0x18, 0x03, 0x20, 0x01, 0x28, 0x03, 0x52, 0x09, 0x72, 0x65, 0x61, 0x64, 0x4c, 0x69, 0x6d, 0x69,
	0x74, 0x12, 0x23, 0x0a, 0x0d, 0x61, 0x72, 0x63, 0x68, 0x69, 0x76, 0x65, 0x5f, 0x65, 0x6e, 0x74,
	0x72, 0x79, 0x18, 0x04, 0x20, 0x01, 0x28, 0x09, 0x52, 0x0c, 0x61, 0x72, 0x63, 0x68, 0x69, 0x76,
	0x65, 0x45, 0x6e, 0x74, 0x72, 0x79, 0x22, 0x29, 0x0a, 0x13, 0x47, 0x65, 0x74, 0x46, 0x69, 0x6c,
	0x65, 0x54, 0x61, 0x69, 0x6c, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x12, 0x12, 0x0a,
	0x04, 0x64, 0x61, 0x74, 0x61, 0x18, 0x01, 0x20, 0x01, 0x28, 0x0c, 0x52, 0x04, 0x64, 0x61, 0x74,
	0x61, 0x32, 0x8a, 0x03, 0x0a, 0x17, 0x52, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x53, 0x74, 0x6f, 0x72,
	0x65, 0x46, 0x69, 0x6c, 0x65, 0x44, 0x6f, 0x77, 0x6e, 0x6c, 0x6f, 0x61, 0x64, 0x12, 0x86, 0x01,
	0x0a, 0x07, 0x47, 0x65, 0x74, 0x46, 0x69, 0x6c, 0x65, 0x12, 0x2e, 0x2e, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x2e, 0x64, 0x65, 0x76, 0x74, 0x6f, 0x6f, 0x6c, 0x73, 0x2e, 0x72, 0x65, 0x73, 0x75,
	0x6c, 0x74, 0x73, 0x74, 0x6f, 0x72, 0x65, 0x2e, 0x76, 0x32, 0x2e, 0x47, 0x65, 0x74, 0x46, 0x69,
	0x6c, 0x65, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x1a, 0x2f, 0x2e, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x2e, 0x64, 0x65, 0x76, 0x74, 0x6f, 0x6f, 0x6c, 0x73, 0x2e, 0x72, 0x65, 0x73, 0x75,
	0x6c, 0x74, 0x73, 0x74, 0x6f, 0x72, 0x65, 0x2e, 0x76, 0x32, 0x2e, 0x47, 0x65, 0x74, 0x46, 0x69,
	0x6c, 0x65, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x22, 0x18, 0x82, 0xd3, 0xe4, 0x93,
	0x02, 0x12, 0x12, 0x10, 0x2f, 0x76, 0x32, 0x2f, 0x7b, 0x75, 0x72, 0x69, 0x3d, 0x66, 0x69, 0x6c,
	0x65, 0x2f, 0x2a, 0x7d, 0x30, 0x01, 0x12, 0x95, 0x01, 0x0a, 0x0b, 0x47, 0x65, 0x74, 0x46, 0x69,
	0x6c, 0x65, 0x54, 0x61, 0x69, 0x6c, 0x12, 0x32, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e,
	0x64, 0x65, 0x76, 0x74, 0x6f, 0x6f, 0x6c, 0x73, 0x2e, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73,
	0x74, 0x6f, 0x72, 0x65, 0x2e, 0x76, 0x32, 0x2e, 0x47, 0x65, 0x74, 0x46, 0x69, 0x6c, 0x65, 0x54,
	0x61, 0x69, 0x6c, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x1a, 0x33, 0x2e, 0x67, 0x6f, 0x6f,
	0x67, 0x6c, 0x65, 0x2e, 0x64, 0x65, 0x76, 0x74, 0x6f, 0x6f, 0x6c, 0x73, 0x2e, 0x72, 0x65, 0x73,
	0x75, 0x6c, 0x74, 0x73, 0x74, 0x6f, 0x72, 0x65, 0x2e, 0x76, 0x32, 0x2e, 0x47, 0x65, 0x74, 0x46,
	0x69, 0x6c, 0x65, 0x54, 0x61, 0x69, 0x6c, 0x52, 0x65, 0x73, 0x70, 0x6f, 0x6e, 0x73, 0x65, 0x22,
	0x1d, 0x82, 0xd3, 0xe4, 0x93, 0x02, 0x17, 0x12, 0x15, 0x2f, 0x76, 0x32, 0x2f, 0x7b, 0x75, 0x72,
	0x69, 0x3d, 0x66, 0x69, 0x6c, 0x65, 0x2f, 0x74, 0x61, 0x69, 0x6c, 0x2f, 0x2a, 0x7d, 0x1a, 0x4e,
	0xca, 0x41, 0x1a, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73, 0x74, 0x6f, 0x72, 0x65, 0x2e, 0x67,
	0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2e, 0x63, 0x6f, 0x6d, 0xd2, 0x41, 0x2e,
	0x68, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x77, 0x77, 0x77, 0x2e, 0x67, 0x6f, 0x6f, 0x67,
	0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2e, 0x63, 0x6f, 0x6d, 0x2f, 0x61, 0x75, 0x74, 0x68, 0x2f,
	0x63, 0x6c, 0x6f, 0x75, 0x64, 0x2d, 0x70, 0x6c, 0x61, 0x74, 0x66, 0x6f, 0x72, 0x6d, 0x42, 0x71,
	0x0a, 0x22, 0x63, 0x6f, 0x6d, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x64, 0x65, 0x76,
	0x74, 0x6f, 0x6f, 0x6c, 0x73, 0x2e, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73, 0x74, 0x6f, 0x72,
	0x65, 0x2e, 0x76, 0x32, 0x50, 0x01, 0x5a, 0x49, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x67,
	0x6f, 0x6c, 0x61, 0x6e, 0x67, 0x2e, 0x6f, 0x72, 0x67, 0x2f, 0x67, 0x65, 0x6e, 0x70, 0x72, 0x6f,
	0x74, 0x6f, 0x2f, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x61, 0x70, 0x69, 0x73, 0x2f, 0x64, 0x65,
	0x76, 0x74, 0x6f, 0x6f, 0x6c, 0x73, 0x2f, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73, 0x74, 0x6f,
	0x72, 0x65, 0x2f, 0x76, 0x32, 0x3b, 0x72, 0x65, 0x73, 0x75, 0x6c, 0x74, 0x73, 0x74, 0x6f, 0x72,
	0x65, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDescOnce sync.Once
	file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDescData = file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDesc
)

func file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDescGZIP() []byte {
	file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDescOnce.Do(func() {
		file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDescData = protoimpl.X.CompressGZIP(file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDescData)
	})
	return file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDescData
}

var file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes = make([]protoimpl.MessageInfo, 4)
var file_google_devtools_resultstore_v2_resultstore_file_download_proto_goTypes = []interface{}{
	(*GetFileRequest)(nil),      // 0: google.devtools.resultstore.v2.GetFileRequest
	(*GetFileResponse)(nil),     // 1: google.devtools.resultstore.v2.GetFileResponse
	(*GetFileTailRequest)(nil),  // 2: google.devtools.resultstore.v2.GetFileTailRequest
	(*GetFileTailResponse)(nil), // 3: google.devtools.resultstore.v2.GetFileTailResponse
}
var file_google_devtools_resultstore_v2_resultstore_file_download_proto_depIdxs = []int32{
	0, // 0: google.devtools.resultstore.v2.ResultStoreFileDownload.GetFile:input_type -> google.devtools.resultstore.v2.GetFileRequest
	2, // 1: google.devtools.resultstore.v2.ResultStoreFileDownload.GetFileTail:input_type -> google.devtools.resultstore.v2.GetFileTailRequest
	1, // 2: google.devtools.resultstore.v2.ResultStoreFileDownload.GetFile:output_type -> google.devtools.resultstore.v2.GetFileResponse
	3, // 3: google.devtools.resultstore.v2.ResultStoreFileDownload.GetFileTail:output_type -> google.devtools.resultstore.v2.GetFileTailResponse
	2, // [2:4] is the sub-list for method output_type
	0, // [0:2] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() { file_google_devtools_resultstore_v2_resultstore_file_download_proto_init() }
func file_google_devtools_resultstore_v2_resultstore_file_download_proto_init() {
	if File_google_devtools_resultstore_v2_resultstore_file_download_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*GetFileRequest); i {
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
		file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*GetFileResponse); i {
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
		file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[2].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*GetFileTailRequest); i {
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
		file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes[3].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*GetFileTailResponse); i {
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
			RawDescriptor: file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   4,
			NumExtensions: 0,
			NumServices:   1,
		},
		GoTypes:           file_google_devtools_resultstore_v2_resultstore_file_download_proto_goTypes,
		DependencyIndexes: file_google_devtools_resultstore_v2_resultstore_file_download_proto_depIdxs,
		MessageInfos:      file_google_devtools_resultstore_v2_resultstore_file_download_proto_msgTypes,
	}.Build()
	File_google_devtools_resultstore_v2_resultstore_file_download_proto = out.File
	file_google_devtools_resultstore_v2_resultstore_file_download_proto_rawDesc = nil
	file_google_devtools_resultstore_v2_resultstore_file_download_proto_goTypes = nil
	file_google_devtools_resultstore_v2_resultstore_file_download_proto_depIdxs = nil
}

// Reference imports to suppress errors if they are not otherwise used.
var _ context.Context
var _ grpc.ClientConnInterface

// This is a compile-time assertion to ensure that this generated file
// is compatible with the grpc package it is being compiled against.
const _ = grpc.SupportPackageIsVersion6

// ResultStoreFileDownloadClient is the client API for ResultStoreFileDownload service.
//
// For semantics around ctx use and closing/ending streaming RPCs, please refer to https://godoc.org/google.golang.org/grpc#ClientConn.NewStream.
type ResultStoreFileDownloadClient interface {
	// Retrieves the File with the given uri.
	// returns a stream of bytes to be stitched together in order.
	//
	// An error will be reported in the following cases:
	// - If the File is not found.
	// - If the given File uri is badly formatted.
	GetFile(ctx context.Context, in *GetFileRequest, opts ...grpc.CallOption) (ResultStoreFileDownload_GetFileClient, error)
	// Retrieves the tail of a File with the given uri.
	//
	// An error will be reported in the following cases:
	// - If the File is not found.
	// - If the given File uri is badly formatted.
	GetFileTail(ctx context.Context, in *GetFileTailRequest, opts ...grpc.CallOption) (*GetFileTailResponse, error)
}

type resultStoreFileDownloadClient struct {
	cc grpc.ClientConnInterface
}

func NewResultStoreFileDownloadClient(cc grpc.ClientConnInterface) ResultStoreFileDownloadClient {
	return &resultStoreFileDownloadClient{cc}
}

func (c *resultStoreFileDownloadClient) GetFile(ctx context.Context, in *GetFileRequest, opts ...grpc.CallOption) (ResultStoreFileDownload_GetFileClient, error) {
	stream, err := c.cc.NewStream(ctx, &_ResultStoreFileDownload_serviceDesc.Streams[0], "/google.devtools.resultstore.v2.ResultStoreFileDownload/GetFile", opts...)
	if err != nil {
		return nil, err
	}
	x := &resultStoreFileDownloadGetFileClient{stream}
	if err := x.ClientStream.SendMsg(in); err != nil {
		return nil, err
	}
	if err := x.ClientStream.CloseSend(); err != nil {
		return nil, err
	}
	return x, nil
}

type ResultStoreFileDownload_GetFileClient interface {
	Recv() (*GetFileResponse, error)
	grpc.ClientStream
}

type resultStoreFileDownloadGetFileClient struct {
	grpc.ClientStream
}

func (x *resultStoreFileDownloadGetFileClient) Recv() (*GetFileResponse, error) {
	m := new(GetFileResponse)
	if err := x.ClientStream.RecvMsg(m); err != nil {
		return nil, err
	}
	return m, nil
}

func (c *resultStoreFileDownloadClient) GetFileTail(ctx context.Context, in *GetFileTailRequest, opts ...grpc.CallOption) (*GetFileTailResponse, error) {
	out := new(GetFileTailResponse)
	err := c.cc.Invoke(ctx, "/google.devtools.resultstore.v2.ResultStoreFileDownload/GetFileTail", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// ResultStoreFileDownloadServer is the server API for ResultStoreFileDownload service.
type ResultStoreFileDownloadServer interface {
	// Retrieves the File with the given uri.
	// returns a stream of bytes to be stitched together in order.
	//
	// An error will be reported in the following cases:
	// - If the File is not found.
	// - If the given File uri is badly formatted.
	GetFile(*GetFileRequest, ResultStoreFileDownload_GetFileServer) error
	// Retrieves the tail of a File with the given uri.
	//
	// An error will be reported in the following cases:
	// - If the File is not found.
	// - If the given File uri is badly formatted.
	GetFileTail(context.Context, *GetFileTailRequest) (*GetFileTailResponse, error)
}

// UnimplementedResultStoreFileDownloadServer can be embedded to have forward compatible implementations.
type UnimplementedResultStoreFileDownloadServer struct {
}

func (*UnimplementedResultStoreFileDownloadServer) GetFile(*GetFileRequest, ResultStoreFileDownload_GetFileServer) error {
	return status.Errorf(codes.Unimplemented, "method GetFile not implemented")
}
func (*UnimplementedResultStoreFileDownloadServer) GetFileTail(context.Context, *GetFileTailRequest) (*GetFileTailResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method GetFileTail not implemented")
}

func RegisterResultStoreFileDownloadServer(s *grpc.Server, srv ResultStoreFileDownloadServer) {
	s.RegisterService(&_ResultStoreFileDownload_serviceDesc, srv)
}

func _ResultStoreFileDownload_GetFile_Handler(srv interface{}, stream grpc.ServerStream) error {
	m := new(GetFileRequest)
	if err := stream.RecvMsg(m); err != nil {
		return err
	}
	return srv.(ResultStoreFileDownloadServer).GetFile(m, &resultStoreFileDownloadGetFileServer{stream})
}

type ResultStoreFileDownload_GetFileServer interface {
	Send(*GetFileResponse) error
	grpc.ServerStream
}

type resultStoreFileDownloadGetFileServer struct {
	grpc.ServerStream
}

func (x *resultStoreFileDownloadGetFileServer) Send(m *GetFileResponse) error {
	return x.ServerStream.SendMsg(m)
}

func _ResultStoreFileDownload_GetFileTail_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(GetFileTailRequest)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(ResultStoreFileDownloadServer).GetFileTail(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/google.devtools.resultstore.v2.ResultStoreFileDownload/GetFileTail",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(ResultStoreFileDownloadServer).GetFileTail(ctx, req.(*GetFileTailRequest))
	}
	return interceptor(ctx, in, info, handler)
}

var _ResultStoreFileDownload_serviceDesc = grpc.ServiceDesc{
	ServiceName: "google.devtools.resultstore.v2.ResultStoreFileDownload",
	HandlerType: (*ResultStoreFileDownloadServer)(nil),
	Methods: []grpc.MethodDesc{
		{
			MethodName: "GetFileTail",
			Handler:    _ResultStoreFileDownload_GetFileTail_Handler,
		},
	},
	Streams: []grpc.StreamDesc{
		{
			StreamName:    "GetFile",
			Handler:       _ResultStoreFileDownload_GetFile_Handler,
			ServerStreams: true,
		},
	},
	Metadata: "google/devtools/resultstore/v2/resultstore_file_download.proto",
}
