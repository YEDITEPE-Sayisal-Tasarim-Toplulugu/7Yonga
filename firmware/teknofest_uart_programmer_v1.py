import os
import sys
import serial
import time
import serial.tools.list_ports
import argparse

UPLOAD_BRATE = 9600
UPLOAD_PORT = "COM1"
UPLOAD_DELAY_MS = 500
DUMMY_INST   = "00000000"

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
    
    lst.extend([DUMMY_INST for _ in range(4-len(lst) % 4)])

    progress_len = len(lst) * 4 
    printProgressBar(0, progress_len, prefix = 'Progress:', suffix = 'Complete', length = 50)
    
    try:
        ser = serial.Serial(UPLOAD_PORT, UPLOAD_BRATE) #, timeout=0, parity=serial.PARITY_EVEN, rtscts=1

        try:
            prog_cur = 0

            # SEND PROG.
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

                    time.sleep(UPLOAD_DELAY_MS / 1000) # Sleep for UPLOAD_SPEED seconds

            while ser.out_waiting > 0:  # Verilerin gerçekten gönderildiğinden emin ol
                pass
            print("tamamdır.")
        except Exception as upload_er:
            print("uploading error:", str(upload_er))

        ser.close()
    except Exception as connection_er:
       print("connection error:", str(connection_er))


####################    USB SEARCH    ########################
ports = serial.tools.list_ports.comports()
for port, desc, hwid in sorted(ports):
    print("{}: {} [{}]".format(port, desc, hwid))
if not len(ports):
    print("Uart port is empty!\nexit.")
    sys.exit()
##############################################################

parser = argparse.ArgumentParser(description='Teknofest ~ UART Programmer v1.0')
parser.add_argument('--version', action='version', version='Teknofest ~ UART Programmer v1.0')
parser.add_argument('--file', dest='file', type=str, help='file: hex file name')
parser.add_argument('--port', dest='port', type=str, help='port: device port name')
parser.add_argument('--brate', dest='brate', type=int, help='brate: connection baud rate')
parser.add_argument('--delay', dest='delay', type=float, help='delay: connection baud rate')
args = parser.parse_args()

hex_file_name = args.file if (args.file is not None) else exit
UPLOAD_BRATE = args.brate if (args.brate is not None) else UPLOAD_BRATE
UPLOAD_PORT = args.port if (args.port is not None) else UPLOAD_PORT
UPLOAD_DELAY_MS = args.delay if (args.delay is not None) else UPLOAD_DELAY_MS

print("File\t\t:", hex_file_name)
print("Baude rate\t:", UPLOAD_BRATE)
print("Port\t\t:", UPLOAD_PORT)

hex_list = []

if (os.path.isfile(hex_file_name)):
    with open(hex_file_name) as f:
        hex_list = f.readlines()

    if len(hex_list):
        print("Bytes\t\t:", (len(hex_list)*4))
        if (input("Do you want to write?(y/n): ").strip() in ["y", "Y"]):
            start_time = time.time() # get time

            write_serial(hex_list)

            end_time = time.time() # get time

            time_lapsed = end_time - start_time # calculate time
            time_convert(time_lapsed) # print time

            print("finished")
        else:
            print("Bye :/")
    else:
        print("empty file")
else:
    print("ERROR: file does not exist")

