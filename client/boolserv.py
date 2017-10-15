# original: https://github.com/uwplse/verdi-raft/blob/master/extraction/vard/bench/vard.py

import socket
import re
import uuid
from select import select
from struct import pack, unpack

def poll(sock, timeout):
    return sock in select([sock], [], [], timeout)[0]

class SendError(Exception):
    pass

class ReceiveError(Exception):
    pass

class LeaderChanged(Exception):
    pass

class Client(object):
    class NoLeader(Exception):
        pass

    @classmethod
    def find_leader(cls, cluster):
        # cluster should be a list of [(host, port)] pairs
        for (host, port) in cluster:
            c = cls(host, port)
            try:
                c.get()
            except LeaderChanged:
                continue
            else:
                return (host, port)
        raise cls.NoLeader

    response_re = re.compile(r'Res\W+([0-9]+)\W+([/A-Za-z0-9]+|-)')

    def __init__(self, host, port, sock=None):
        if not sock:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.connect((host, port))
        else:
            self.sock = sock
        self.request_id = 0

    def deserialize(self, data):
        if data == '-':
            return None
        return data

    def serialize(self, arg):
        if arg is None:
            return '-'
        return str(arg)

    def send_command(self, cmd, arg=None):
        msg = str(self.request_id) + ' ' + cmd + ' ' + self.serialize(arg)
        n = self.sock.send(pack("<I", len(msg)))
        if n < 4:
            raise SendError
        else:
            self.sock.send(msg)
            self.request_id += 1

    def parse_response(self, data):
        if data.startswith('NotLeader'):
            raise LeaderChanged
        try:
            match = self.response_re.match(data)
            return [self.deserialize(match.group(n)) for n in (1,2)]
        except Exception as e:
            print "Parse error, data=%s" % data
            raise e

    def process_response(self):
        len_bytes = self.sock.recv(4)
        if len_bytes == '':
            raise ReceiveError
        else:
            len_msg = unpack("<I", len_bytes)[0]
            data = self.sock.recv(len_msg)
            if data == '':
                raise ReceiveError
            else:
                return self.parse_response(data)

    def get(self):
        self.send_command('GET')
        return self.process_response()[1]

    def get_no_wait(self):
        self.send_command('GET')

    def put_no_wait(self, v):
        self.send_command('PUT', v)

    def put(self, v):
        self.send_command('PUT', v)
        return self.process_response()[1]
