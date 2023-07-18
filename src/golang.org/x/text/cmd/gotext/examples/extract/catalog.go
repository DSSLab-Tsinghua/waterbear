// Code generated by running "go generate" in golang.org/x/text. DO NOT EDIT.

package main

import (
	"golang.org/x/text/language"
	"golang.org/x/text/message"
	"golang.org/x/text/message/catalog"
)

type dictionary struct {
	index []uint32
	data  string
}

func (d *dictionary) Lookup(key string) (data string, ok bool) {
	p, ok := messageKeyToIndex[key]
	if !ok {
		return "", false
	}
	start, end := d.index[p], d.index[p+1]
	if start == end {
		return "", false
	}
	return d.data[start:end], true
}

func init() {
	dict := map[string]catalog.Dictionary{
		"de":    &dictionary{index: deIndex, data: deData},
		"en_US": &dictionary{index: en_USIndex, data: en_USData},
		"zh":    &dictionary{index: zhIndex, data: zhData},
	}
	fallback := language.MustParse("en-US")
	cat, err := catalog.NewFromMap(dict, catalog.Fallback(fallback))
	if err != nil {
		panic(err)
	}
	message.DefaultCatalog = cat
}

var messageKeyToIndex = map[string]int{
	"%.2[1]f miles traveled (%[1]f)":                 8,
	"%[1]s is visiting %[3]s!\n":                     3,
	"%d files remaining!":                            5,
	"%d more files remaining!":                       4,
	"%s is out of order!":                            7,
	"%s is visiting %s!\n":                           2,
	"Hello %s!\n":                                    1,
	"Hello world!\n":                                 0,
	"Use the following code for your discount: %d\n": 6,
}

var deIndex = []uint32{ // 10 elements
	0x00000000, 0x00000011, 0x00000023, 0x0000003d,
	0x00000057, 0x00000076, 0x00000076, 0x00000076,
	0x00000076, 0x00000076,
} // Size: 64 bytes

const deData string = "" + // Size: 118 bytes
	"\x04\x00\x01\x0a\x0c\x02Hallo Welt!\x04\x00\x01\x0a\x0d\x02Hallo %[1]s!" +
	"\x04\x00\x01\x0a\x15\x02%[1]s besucht %[2]s!\x04\x00\x01\x0a\x15\x02%[1]" +
	"s besucht %[3]s!\x02Noch %[1]d Bestände zu gehen!"

var en_USIndex = []uint32{ // 10 elements
	0x00000000, 0x00000012, 0x00000024, 0x00000042,
	0x00000060, 0x000000a3, 0x000000ba, 0x000000ef,
	0x00000106, 0x00000125,
} // Size: 64 bytes

const en_USData string = "" + // Size: 293 bytes
	"\x04\x00\x01\x0a\x0d\x02Hello world!\x04\x00\x01\x0a\x0d\x02Hello %[1]sn" +
	"\x04\x00\x01\x0a\x19\x02%[1]s is visiting %[2]s!\x04\x00\x01\x0a\x19\x02" +
	"%[1]s is visiting %[3]s!\x14\x01\x81\x01\x00\x02\x14\x02One file remaini" +
	"ng!\x00&\x02There are %[1]d more files remaining!\x02%[1]d files remaini" +
	"ng!\x04\x00\x01\x0a0\x02Use the following code for your discount: %[1]d" +
	"\x02%[1]s is out of order!\x02%.2[1]f miles traveled (%[1]f)"

var zhIndex = []uint32{ // 10 elements
	0x00000000, 0x00000000, 0x00000000, 0x00000000,
	0x00000000, 0x00000000, 0x00000000, 0x00000000,
	0x00000000, 0x00000000,
} // Size: 64 bytes

const zhData string = ""

// Total table size 603 bytes (0KiB); checksum: 1D2754EE
