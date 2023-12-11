import sys
import matplotlib.pyplot as plt
import numpy as np
from tabulate import tabulate

def items_from_line(line):
    items = line.strip().split(" ")
    items = list(filter(lambda x: x != "", items))
    return items

def parse_table(lines, index):
    if "verus" in lines[index]: 
        lang = "verus"
    else:
        assert "dafny" in lines[index]
        lang = "dafny"
    index += 1

    assert lines[index].startswith("---  ")
    index += 1

    items = items_from_line(lines[index])
    header = [i + "_" + lang for i in items[1:]]
    data = []

    while 1:
        index += 1
        line = lines[index]
        if line.startswith("---  "):
            break
        items = items_from_line(line)
        items = [float(i) for i in items]
        data.append(items)
    return index, np.array(data), header

def parse_log(path):
    f = open(path + "/log.txt", "r")
    lines = f.readlines()
    f.close()

    index = 0

    datas = []
    headers = []

    while index < len(lines):
        line = lines[index]
        
        if line.startswith("[INFO] rerun summary "):
            index, data, header = parse_table(lines, index)
            datas += [data]
            headers.extend(header)
        index += 1

    fig, ax = plt.subplots()
    vdata = datas[0]
    ddata = datas[1][:, 1:]
    data = np.hstack((vdata, ddata))
    headers = ["asserts"] + headers
    table = [headers]

    for i in range(0, len(data)):
        table.append(list(data[i,:]))
    print(tabulate(table, headers="firstrow"))

    for i in range(1, len(headers)):
        marker = "o" if "INST" in headers[i] else "x"
        ax.plot(data[:, 0], data[:, i], label=headers[i], marker=marker)
    ax.set_xlabel("number of asserts")
    ax.set_ylabel("time (s)")
    ax.legend()
    plt.savefig(path + "/log.png", dpi=300)

parse_log(sys.argv[1])
