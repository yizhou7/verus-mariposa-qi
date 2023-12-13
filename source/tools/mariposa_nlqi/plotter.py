import sys, os
import matplotlib.pyplot as plt
import numpy as np
from tabulate import tabulate
from enum import Enum

def items_from_line(line):
    items = line.strip().split(" ")
    items = list(filter(lambda x: x != "", items))
    return items

def smt_result_as_int(result):
    if result == "unsat":
        return 0
    elif result == "unknown":
        return 2
    elif result == "timeout":
        return 3
    assert False

def smt_result_from_int(result):
    result = int(result)
    if result == 0:
        return "unsat"
    elif result == 2:
        return "unknown"
    elif result == 3:
        return "timeout"
    assert False

def pretty_print_data(data, headers):
    table = [headers]
    # print(data.shape)
    for i in range(0, len(data)):
        table.append(list(data[i,:]))
    new_table = [table[0]]
    for i in range(1, len(table)):
        row = [table[i][0][0]]
        for j in range(1, len(table[i])):
            item = table[i][j]
            assert len(item) == 2
            item = f"{item[0]:.2f} {smt_result_from_int(item[1])}"
            row.append(item)
        new_table.append(row)
    print(tabulate(new_table, headers="firstrow"))

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
    rows = []

    while 1:
        index += 1
        line = lines[index]
        if line.startswith("---  "):
            break
        items = items_from_line(line)
        id = float(items[0])
        row = [id, id]
        for i in range(1, len(items)):
            item = items[i]
            if item.startswith("("):
                row.append(float(item[1:-1]))
            elif item.endswith(")"):
                row.append(smt_result_as_int(item[1:-2]))
        row = list(zip(row[::2], row[1::2]))
        rows.append(row)
    return index, np.array(rows), header

def parse_log(proj_root):
    f = open(proj_root + "/log.txt", "r")
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

    for i in range(1, len(headers)):
        marker = "o" if "INST" in headers[i] else "x"
        ax.plot(data[:, 0, 0], data[:, i, 0], label=headers[i], marker=marker)
    ax.set_xlabel("number of asserts")
    ax.set_ylabel("time (s)")
    ax.legend()
    plt.savefig(proj_root + "/log.png", dpi=300)

    return data, headers

def get_column_stats(column):
    num_timeouts = 0
    first_timeout = len(column) + 1
    for i in range(len(column)):
        if smt_result_from_int(column[i][1]) == "timeout":
            if first_timeout == len(column) + 1:
                first_timeout = i + 2
            num_timeouts += 1
    return num_timeouts, first_timeout

def get_proj_stats(data, headers):
    # pretty_print_data(data, headers)
    stats = {headers[i]: None for i in range(1, len(headers))}
    # print(num_timeouts)
    for i in range(1, len(data[0])):
        column = data[1:, i]
        num_timeouts, first_timeout = get_column_stats(column)
        # print(headers[i], num_timeouts, first_timeout)
        stats[headers[i]] = [(num_timeouts, first_timeout)]
    return stats

def stat_multiple(path):
    all_stats = None
    sample_count = 0
    for proj_root in os.listdir(path):
        proj_root = path + "/" + proj_root
        if os.path.isdir(proj_root):
            # print(proj_root)
            data, headers = parse_log(proj_root)
            stats = get_proj_stats(data, headers)
            if all_stats == None:
                all_stats = stats
            else:
                assert all_stats.keys() == stats.keys()
                for k in stats:
                    all_stats[k].extend(stats[k])
            sample_count += 1
    print("number of samples", sample_count)
    table = [["mode", "num_TO (mean)", "first_TO (mean)"]]
    for k in all_stats:
        mode_stats = np.array(all_stats[k])
        table += [[k, np.round(np.mean(mode_stats[:,0]), 2), np.round(np.mean(mode_stats[:,1]), 2)]]
    print(tabulate(table, headers="firstrow"))

if __name__ == "__main__":
    path = sys.argv[1]
    log_path = path + "/log.txt"
    if os.path.exists(log_path):
        data, headers = parse_log(path)
        pretty_print_data(data, headers)
    else:
        stat_multiple(path)
