import ParseItExamples.Roman

#guard "MCMLXXXVII".toNatRoman? == some 1987
#guard "MMMCMXCIX".toNatRoman? == some 3999
#guard "XC".toNatRoman? == some 90
#guard "XLIV".toNatRoman? == some 44
#guard "CDXCIX".toNatRoman? == some 499
#guard "mmxxvi".toNatRoman? (upper := false) == some 2026
#guard "mmxxvi".toNatRoman? == none
#guard "IIII".toNatRoman? == none
#guard "IC".toNatRoman? == none
#guard "".toNatRoman? == none
