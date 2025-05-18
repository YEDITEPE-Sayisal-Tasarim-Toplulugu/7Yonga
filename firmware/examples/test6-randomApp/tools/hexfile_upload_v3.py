import os
import serial
import time
import serial.tools.list_ports
import argparse

START_BYTE = "start_byte"
BYTE_COUNT = "byte_count"
ADDRESS_VALUE = "address_value"
RECORD_TYPE = "record_type"
DATA_BYTES = "data_bytes"
CHECKSUM_BYTE = "checksum_bytes"
CODES_LIST = "codes_list"

UPLOAD_BRATE = 9600
UPLOAD_PORT = "COM1"
UPLOAD_DELAY_MS = 500
UPLOAD_FIFO_LENGHT = 10
UPLOAD_DATA_MAX = 1000
UPLOAD_RESPONSE_DATA = "FA"

program_upload = True

def replace_code(lst):
    for i in range(len(lst)):
        if lst[i] == "37A00000":
            lst[i] = "FF000000"
        lst[i] = lst[i][6:8] + lst[i][4:6] + lst[i][2:4] + lst[i][0:2]
    return lst

def hex_line_parse(hexline):
    byte_count = int(hexline[1:3], 16)
    data_bytes = hexline[9:(9+byte_count*2)]
    checksum_byte = hexline[-3:-1]

    # checking hexline data
    # firstly, add all bytes without checksum byte(last two byte)
    # then for intel hex : calculate the two's complement of that
    # finally compare calculated value and checksum byte
    bytes_sum = sum([int(hexline[i:i+2], 16) for i in range(1, len(hexline)-3, 2)])
    if (((1<<32)-bytes_sum)&0xFF) != int(checksum_byte, 16):
        print("hex line error: ", hexline)
        return []
    
    # creating hex code from data in the hex file
    rw = data_bytes + ("" if (len(data_bytes) == 8*4 or not len(data_bytes) % 8) else ((8 - len(data_bytes) % 8)*'0'))
    codes = ([rw[s * 8 : s * 8 + 8] for s in range(0, int(len(rw) / 8))])
    codes = replace_code(codes)

    return {
        BYTE_COUNT : byte_count,
        ADDRESS_VALUE : hexline[3:7],
        RECORD_TYPE : hexline[7:9],
        DATA_BYTES : data_bytes,
        CHECKSUM_BYTE : checksum_byte,
        CODES_LIST : codes,
    }

# APLOADER #

def time_convert(sec):
    mins = sec // 60
    sec = sec % 60
    hours = mins // 60
    mins = mins % 60
    # print("Time Lapsed = {0}:{1}:{2}".format(int(hours),int(mins),sec))
    print("Time Lapsed = {0} minutes {1} second".format(int(mins), sec))

"""
https://stackoverflow.com/questions/3173320/text-progress-bar-in-terminal-with-block-characters/13685020
Call in a loop to create terminal progress bar
@params:
    iteration   - Required  : current iteration (Int)
    total       - Required  : total iterations (Int)
    prefix      - Optional  : prefix string (Str)
    suffix      - Optional  : suffix string (Str)
    decimals    - Optional  : positive number of decimals in percent complete (Int)
    length      - Optional  : character length of bar (Int)
    fill        - Optional  : bar fill character (Str)
    printEnd    - Optional  : end character (e.g. "\r", "\r\n") (Str)
"""
def printProgressBar (iteration, total, prefix = '', suffix = '', decimals = 1, length = 100, fill = '█', printEnd = "\r"):
    percent = ("{0:." + str(decimals) + "f}").format(100 * (iteration / float(total)))
    filledLength = int(length * iteration // total)
    bar = fill * filledLength + '-' * (length - filledLength)
    print(f'\r{prefix} |{bar}| {percent}% {suffix}', end = printEnd)
    # Print New Line on Complete
    if iteration == total: 
        print()

def write_serial(lst):
    print("writing...")
    
    progress_len = len(lst) * 4 
    printProgressBar(0, progress_len, prefix = 'Progress:', suffix = 'Complete', length = 50)
    
    try:
        ser = serial.Serial(UPLOAD_PORT, UPLOAD_BRATE) #, timeout=0, parity=serial.PARITY_EVEN, rtscts=1

        try:
            prog_cur = 0
            
            for item in lst:
                item = item[6:8] + item[4:6] + item[2:4] + item[0:2]
                for i in range(4):                    
                    send_d = item[i * 2 : i * 2 + 2]
                    
                    #############
                    # send data #
                    byte_to_send = bytes.fromhex(send_d)  # convert the hex string to a bytes object
                    ser.write(byte_to_send)
                    #############

                    # print(send_d)

                    prog_cur += 1
                    printProgressBar(prog_cur, progress_len, prefix = 'Progress:', suffix = 'Complete', length = 50)

                    if (prog_cur % UPLOAD_DATA_MAX == 0):
                        while (ser.read(1) != bytes.fromhex(UPLOAD_RESPONSE_DATA)):
                            pass

                    time.sleep(UPLOAD_DELAY_MS / 1000) # Sleep for UPLOAD_SPEED seconds
                            
                
        except Exception as upload_er:
            print("uploading error:", str(upload_er))

        ser.close()
    except Exception as connection_er:
       print("connection error:", str(connection_er))

####################    USB SEARCH    ########################
ports = serial.tools.list_ports.comports()

for port, desc, hwid in sorted(ports):
        print("{}: {} [{}]".format(port, desc, hwid))
##############################################################

parser = argparse.ArgumentParser()
parser.add_argument('--version', action='version', version='F Company ~ HEX file uploader v3.0')
parser.add_argument('--file', dest='file', type=str, help='file: hex file name')
parser.add_argument('--out', dest='out', type=str, help='file: hex out file name')
parser.add_argument('--port', dest='port', type=str, help='port: device port name')
parser.add_argument('--brate', dest='brate', type=int, help='brate: connection baud rate')
parser.add_argument('--delay', dest='delay', type=float, help='delay: connection baud rate')
args = parser.parse_args()

hex_file_name = args.file if (args.file is not None) else exit
hexdump_file_name = args.out if (args.file is not None) else (hex_file_name + "d")
UPLOAD_BRATE = args.brate if (args.brate is not None) else UPLOAD_BRATE
UPLOAD_PORT = args.port if (args.port is not None) else UPLOAD_PORT
UPLOAD_DELAY_MS = args.delay if (args.delay is not None) else UPLOAD_DELAY_MS

print("File\t\t:", hex_file_name)
print("Baude rate\t:", UPLOAD_BRATE)
print("Port\t\t:", UPLOAD_PORT)

hex_list = []

if (os.path.isfile(hex_file_name)):
    if hex_file_name.endswith(".hex"):
        hlines = []
        
        with open(hex_file_name) as f:
            hlines = f.readlines()

        hex_lines = [hex_line_parse(x) for x in hlines]
        
        addr=0
        for hline in hex_lines:
            if hline[RECORD_TYPE] != "00":
                continue

            insert_data_count = 0
            for t in range(int((int(hline[ADDRESS_VALUE], 16) - addr) / 4)):
                hex_list.append("0"*8)
                insert_data_count += 4
            
            for ls in hline[CODES_LIST]:
                hex_list.append(ls)

            addr += (len(hline[CODES_LIST]) * 4) + insert_data_count
        
        with open(hexdump_file_name, 'w') as file:
            for l in hex_list:
                file.write(l+"\n")
    elif hex_file_name.endswith(".shex"):
        with open(hex_file_name) as f:
            hex_list = f.readlines()

    if len(hex_list):
        #for a in range(16):
        #    hex_list.append("0"*8)

        print("Bytes\t\t:", (len(hex_list)*4))
        if (input("Do you want to write?(y/n): ") in ["y", "Y"]):
            start_time = time.time() # get time

            write_serial(hex_list)

            end_time = time.time() # get time

            time_lapsed = end_time - start_time # calculate time
            time_convert(time_lapsed) # print time

            print("finished")
        else:
            print("Bye :/")
    else:
        print("file type error")
else:
    print("ERROR: file does not exist")
