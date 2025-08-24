import os
import argparse

parser = argparse.ArgumentParser(description='Teknofest ~ DumpedHex generator v1.0')
parser.add_argument('--version', action='version', version='Teknofest ~ DumpedHex generator v1.0')
parser.add_argument('--bin', dest='file_bin', type=str, help='file: bin file name')
parser.add_argument('--o' , dest='out_file', type=str, help='file: out file name')
parser.add_argument('--t' , dest='file_type', type=str, help='type: out file type (hexd/mem)')

args = parser.parse_args()
binFile = args.file_bin
ofile = args.out_file
filetype = args.file_type

if (os.path.isfile(binFile)):
    binFile_op = open(binFile, "rb")
    binData = binFile_op.read()
        
    hexdFile_op = open(ofile, 'w')
    i=0

    print("Byte:", len(binData))

    while (i < len(binData)):
        dat = binData[i : i+4]
        dst = "%02x%02x%02x%02x\n" % ((dat[3] if (len(dat) > 3) else 0), (dat[2] if (len(dat) > 2) else 0), (dat[1] if (len(dat) > 1) else 0), dat[0])
        hexdFile_op.write(dst)
        i+=4

    binFile_op.close()
    hexdFile_op.close()
else:
	print("could not found this file")
