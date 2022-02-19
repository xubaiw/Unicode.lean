import Std.Data.HashMap
import Unicode.IncludeDataFile

set_option maxHeartbeats 200000 in
def foo := include_data_file "./UCD/UnicodeData.txt"