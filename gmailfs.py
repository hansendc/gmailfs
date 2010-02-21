#!/usr/bin/python
#@+leo-ver=4
#@+node:@file gmailfs.py
#@@first
#
#    Copyright (C) 2004  Richard Jones  <richard followed by funny at sign then jones then a dot then name>
#    Copyright (C) 2010  Dave Hansen <dave@sr71.net>
#
#    GmailFS - Gmail Filesystem Version 0.8.6
#    This program can be distributed under the terms of the GNU GPL.
#    See the file COPYING.
#
# TODO:
# Problem: a simple write ends up costing at least 3 server writes:
# 	1. create directory entry
# 	2. create inode
# 	3. create first data block
# It would be greate if files below a certain size (say 64k or something)
# could be inlined and just stuck as an attachment inside the inode.
# It should not be too big or else it will end up making things like
# stat() or getattr() much more expensive
#
# It would also be nice to be able to defer actual inode creation for
# a time.  dirents are going to be harder because we look them up more,
# but inodes should be easier to keep consistent
#
# Wrap all of the imap access functions up better so that we
# can catch the places to invalidate the caches better.
#
# Are there any other options for storing messages than in base64-encoded
# attachments?  I'm worried about the waste of space and bandwidth.  It
# appears to be about a 30% penalty.
#
# Be more selective about clearing the rsp cache.  It is a bit heavy-handed
# right now.
#
# CATENATE
# See if anybody supports this: http://www.faqs.org/rfcs/rfc4469.html
# It would be wonderful when only writing parts of small files, or even
# when updating inodes.
#
# MUTIAPPEND
# With this: http://www.faqs.org/rfcs/rfc3502.html
# we could keep track of modified inodes and submit them in batches back
# to the server
#
# Could support "mount -o ro" or "mount -o remount,ro" with a read-only
# selection of the target mailbox
#
# There some tangling up here of inodes only having a single path
#

"""
GmailFS provides a filesystem using a Google Gmail account as its storage medium
"""

#@+others
#@+node:imports

import pprint
import fuse
import imaplib
import email
from email import encoders
from email.mime.multipart import MIMEMultipart
from email.MIMEText import MIMEText 
from email.mime.base import MIMEBase


import Queue
from fuse import Fuse
import os
from threading import Thread
import threading
import thread
from errno import *
from stat import *
from os.path import abspath, expanduser, isfile

fuse.fuse_python_api = (0, 2)


import thread
import quopri
from lgconstants import *

import sys,traceback,re,string,time,tempfile,array,logging,logging.handlers

#@-node:imports

# Globals
DefaultUsername = 'defaultUser'
DefaultPassword = 'defaultPassword'
DefaultFsname = 'gmailfs'
References={}

IMAPBlockSize = 1024

# this isn't used yet
InlineInodeMax = 32 * 1024

# I tried 64MB for this, but the base64-encoded
# blocks end up about 90MB per message, which is
# a bit too much.
DefaultBlockSize = 16 * 1024 * 1024


SystemConfigFile = "/etc/gmailfs/gmailfs.conf"
UserConfigFile = abspath(expanduser("~/.gmailfs.conf"))

GMAILFS_VERSION = '5'

PathStartDelim  = '__a__'
PathEndDelim    = '__b__'
FileStartDelim  = '__c__'
FileEndDelim    = '__d__'
LinkStartDelim  = '__e__'
LinkEndDelim    = '__f__'
MagicStartDelim = '__g__'
MagicEndDelim   = '__h__'
InodeSubjectPrefix = 'inode_msg'
DirentSubjectPrefix = 'dirent_msg'

InodeTag ='i'
DevTag = 'd'
NumberLinksTag = 'k'
FsNameTag = 'q'
ModeTag = 'e'
UidTag = 'u'
GidTag = 'g'
SizeTag = 's'
AtimeTag = 'a'
MtimeTag = 'm'
CtimeTag = 'c'
BSizeTag = 'z'
VersionTag = 'v'
SymlinkTag = 'l'

RefInodeTag = 'r'
FileNameTag = 'n'
PathNameTag = 'p'

NumberQueryRetries = 1

regexObjectTrailingMB = re.compile(r'\s?MB$')

rsp_cache_hits = 0
rsp_cache_misses = 0
rsp_cache = {}

debug = 1
if debug >= 3:
	imaplib.Debug = 3
#imaplib.Debug = 4

def log_error(str):
	log.debug(str)
	log.error(str)
	sys.stdout.write(str+"\n")
	sys.stderr.write(str+"\n")
	return

def log_debug(str):
	log_debug3(str)
	#str += "\n"
	#sys.stderr.write(str)
	return

def log_entry(str):
	#print str
	log_debug1(str)

writeout_threads = {}
def am_lead_thread():
	if writeout_threads.has_key(thread.get_ident()):
		return 0
	return 1

def log_debug1(str):
	log_info(str)
	#str += "\n"
	#sys.stderr.write(str)
	return

def log_debug2(str):
	if debug >= 2:
		log_info(str)
	return

def log_debug3(str):
	if debug >= 3:
		log_info(str)
	return

def log_imap(str):
	log_debug2("IMAP: " + str)

def log_imap2(str):
	log_debug2("IMAP: " + str)

def log_info(s):
	if not am_lead_thread():
		return
	log.info("[%.2f] %s" % (time.time(), s))
	#print str
	#str += "\n"
	#sys.stderr.write(str)
	return

def log_warning(str):
	log.warning(str)
	#str += "\n"
	#sys.stderr.write(str)
	return

def parse_path(path):
	# should we check that there's always a / in the path??
	ind = string.rindex(path, '/')
	parent_dir = path[:ind]
        filename = path[ind+1:]
	if len(parent_dir) == 0:
		parent_dir = "/"
	return parent_dir, filename


def msg_add_payload(msg, payload, filename=None):
	attach_part = MIMEBase('file', 'attach')
	attach_part.set_payload(payload)
	if filename != None:
		attach_part.add_header('Content-Disposition', 'attachment; filename="%s"' % filename)
	encoders.encode_base64(attach_part)
	msg.attach(attach_part)

# This probably doesn't need to be handed the fsNameVar
# and the username
def mkmsg(subject, preamble, attach = ""):
	global username
	global fsNameVar
	msg = MIMEMultipart()
	log_debug2("mkmsg('%s', '%s', '%s', '%s',...)" % (username, fsNameVar, subject, preamble))
	msg['Subject'] = subject
	msg['To'] = username
	msg['From'] = username
	msg.preamble = preamble
	if len(attach):
		log_debug("attaching %d byte file contents" % len(attach))
		msg_add_payload(msg, attach)
	log_debug3("mkmsg() after subject: '%s'" % (msg['Subject']))
	msg.uid = -1
	return msg

imap_times = {}
imap_times_last_print = 0
def log_imap_time(cmd, start_time):
	global imap_times
	global imap_times_last_print
	if not imap_times.has_key(cmd):
		imap_times[cmd] = 0.0

	now = time.time()
	end_time = now
	duration = end_time - start_time
	imap_times[cmd] += duration
	imap_times_print()

def imap_times_print(force=0):
	global imap_times
	global imap_times_last_print
	now = time.time()
	if force or (now - imap_times_last_print > 10):
		for key, total in imap_times.items():
			log_info("imap_times[%s]: %d" % (key, total))
		imap_times_last_print = now


# The IMAP uid commands can take multiple uids and return
# multiple results
#
# uid here is intended to be an array of uids, and this
# returns a dictionary of results indexed by uid
#
# does python have a ... operator like c preprocessor?
def uid_cmd(imap, cmd, uids, arg1, arg2 = None, arg3 = None):
	imap.lock.acquire()
	ret = __uid_cmd(imap, cmd, uids, arg1, arg2, arg3)
	imap.lock.release()
	return ret

def __uid_cmd(imap, cmd, uids, arg1, arg2 = None, arg3 = None):
	uids_str = string.join(uids, ",")
	start = time.time()
	log_info("__uid_cmd(%s,...)" % (cmd))
    	rsp, rsp_data = imap.uid(cmd, uids_str, arg1, arg2, arg3)
	log_imap_time(cmd, start);
	log_info("__uid_cmd(%s, [%s]) ret: '%s'" % (cmd, uids_str, rsp))
	if rsp != "OK":
		log_error("IMAP uid cmd (%s) error: %s" % (cmd, rsp))
		return None
	ret = {}
	uid_index = 0
	for rsp_nr in range(len(rsp_data)):
		data = rsp_data[rsp_nr]
		# I don't know if this is expected or
		# not, but every other response is just
		# a plain ')' char.  Skip them
		#
		# should I use isinstance?
		if data == ")":
			continue
		uid = uids[uid_index]
		uid_index += 1
		if data == None:
			log_info("uid_cmd(%s) got strange result %s/%s" % 
					(cmd, rsp_nr, range(len(rsp_data))))
			continue
		desc = data[0]
		result = data[1]
		ret[uid] = result
	return ret

def clear_rsp_cache():
	global rsp_cache
	log_debug2("clearing rsp cache with %d entries" % (len(rsp_cache)))
	rsp_cache = {}

def imap_trash_uids(imap, raw_uids):
	clear_rsp_cache()
	checked_uids = []
	# there have been a few cases where a -1
	# creeps in here because we're trying to
	# delete a message that has not yet been
	# uploaded to the server.  Filter those
	# out.
	for uid in raw_uids:
		if int(uid) <= 0:
			continue
		checked_uids.append(uid)

	if len(checked_uids) == 0:
		return
	log_imap("imap_trash_uids(%s)" % (string.join(checked_uids,",")))
	ret = uid_cmd(imap, "STORE", checked_uids, '+FLAGS', '\\Deleted')
	global msg_cache
	for uid in checked_uids:
		try:
			del msg_cache[uid]
		except:
			foo = 1
			# this is OK because the msg may neve have
			# been cached
	return ret

def imap_trash_msg(imap, msg):
	if msg.uid <= 0:
		return
	imap_trash_uids(imap, [str(msg.uid)])

def imap_append(info, imap, msg):
	#gmsg = libgmail.GmailComposedMessage(username, subject, body)
	log_imap("imap_append(%s)" % (info))
	log_debug2("append Subject: ->%s<-" % (msg['Subject']))
	log_debug3("entire message: ->%s<-" % str(msg))

	now = imaplib.Time2Internaldate(time.time())
	clear_rsp_cache()
	start = time.time()
	imap.lock.acquire()
    	rsp, data = imap.append(fsNameVar, "", now, str(msg))
	imap.lock.release()
	log_imap_time("APPEND", start);
	log_imap2("append for '%s': rsp,data: '%s' '%s'" % (info, rsp, data))
	if rsp != "OK":
		return -1
	# data looks like this: '['[APPENDUID 631933985 286] (Success)']'
	msgid = int((data[0].split()[2]).replace("]",""))
	msg.uid = msgid
	log_debug("imap msgid: '%d'" % msgid)
	return msgid

def _addLoggingHandlerHelper(handler):
    """ Sets our default formatter on the log handler before adding it to
        the log object. """
    handler.setFormatter(defaultLogFormatter)
    log.addHandler(handler)

def GmailConfig(fname):
    import ConfigParser
    cp = ConfigParser.ConfigParser()
    global References
    global DefaultUsername, DefaultPassword, DefaultFsname
    global NumberQueryRetries
    if cp.read(fname) == []:
      log_warning("Unable to read configuration file: " + str(fname))
      return

    sections = cp.sections()
    if "account" in sections:
      options = cp.options("account")
      if "username" in options:
          DefaultUsername = cp.get("account", "username")
      if "password" in options:
          DefaultPassword = cp.get("account", "password")
    else:
      log.error("Unable to find GMail account configuration")

    if "filesystem" in sections:
      options = cp.options("filesystem")
      if "fsname" in options:
          DefaultFsname = cp.get("filesystem", "fsname")
    else:
      log_warning("Using default file system (Dangerous!)")
      
    if "logs" in sections:
      options = cp.options("logs")
      if "level" in options:
        level = cp.get("logs", "level")
        log.setLevel(logging._levelNames[level])
      if "logfile" in options:
        logfile = abspath(expanduser(cp.get("logs", "logfile")))
	log.removeHandler(defaultLoggingHandler)
        _addLoggingHandlerHelper(logging.handlers.RotatingFileHandler(logfile, "a", 5242880, 3))

    if "references" in sections:
      options = cp.options("references")
      for option in options:
          record = cp.get("references",option)
          fields = record.split(':')
          if len(fields)<1 or len(fields)>3:
              log_warning("Invalid reference '%s' in configuration." % (record))
              continue
          reference = reference_class(*fields)
          References[option] = reference

do_writeout = 1
#@+node:mythread
class testthread(Thread):
	def __init__ (self, fs, nr):
		Thread.__init__(self)
		self.fs = fs
		self.nr = nr

	def write_out_object(self):
		try:
			# block, and timeout after 1 second
			object = self.fs.dirty_objects.get(1, 1)
		except:
			# effectively success
			return 0
		# we do not want to sit here sleeping on objects
		# so if we can not get the lock, move on to another
		# object
		got_lock = object.writeout_lock.acquire(0)
		if not got_lock:
			self.fs.dirty_objects.put(object)
			return -1
		reason = Dirtyable.dirty_reason(object)
		write_out_nolock(object, "bdflushd")
		object.writeout_lock.release()
		size = self.fs.dirty_objects.qsize()
		print("[%d] wrote out %s, because '%s' %d left" % (thread.get_ident(), object.to_str(), reason, size))
		return 0

	def run(self):
		global do_writeout
		writeout_threads[thread.get_ident()] = 1
		log_debug1("mythread: started pid: %d" % (os.getpid()))
		print "connected"
		log_debug1("connected")
		while do_writeout:
			tries = 5
			for try_nr in range(tries):
				ret = self.write_out_object()
				if ret == 0:
					break
				# this will happen when there are
				# objects in the queue for which
				# we can not get the lock.  Do
				# not spin, sleep instead
				if try_nr >= tries-1:
					time.sleep(1)

	       	print "mythread done"

    #@-node:mythread


class reference_class:
    def __init__(self,fsname,username=None,password=None):
      self.fsname = fsname
      if username is None or username == '':
          self.username = DefaultUsername
      else:
          self.username = username
      if password is None or password == '':
          self.password = DefaultPassword
      else:
          self.password = password

# This ensures backwards compatability where
# old filesystems were stored with 7bit encodings
# but new ones are all quoted printable
def fixQuotedPrintable(body):
    # first remove headers
    newline = body.find("\r\n\r\n")
    if newline >= 0:
	body = body[newline:]
    fixed = body
    if re.search("Content-Transfer-Encoding: quoted",body):
        fixed = quopri.decodestring(body)
    # Map unicode     
    return fixed.replace('\u003d','=')

def psub(s):
    if len(s) == 0:
	return "";
    return "SUBJECT \""+s+"\""

def _getMsguidsByQuery(about, imap, queries, or_query = 0):
    or_str = ""
    if or_query:
	or_str = " OR"
    fsq = (str(FsNameTag + "=" + MagicStartDelim + fsNameVar + MagicEndDelim))
    # this is *REALLY* sensitive, at least on gmail
    # Don't put any extra space in it anywhere, or you
    # will be sorry
    #  53:12.12 > MGLK6 SEARCH (SUBJECT "foo=bar" SUBJECT "bar=__fo__o__")
    queryString  = '(SUBJECT "%s"' % (fsq)
    last_q = queries.pop()
    for q in queries:
    	queryString += or_str + ' SUBJECT "%s"' % (q)
    queryString += ' SUBJECT "%s")' % last_q

    global rsp_cache
    global rsp_cache_hits
    global rsp_cache_misses
    if rsp_cache_hits+rsp_cache_misses % 10 == 0:
	    log_info("rsp_cache (size: %d hits: %d misses: %d)" % (len(rsp_cache), rsp_cache_hits, rsp_cache_misses))
    if rsp_cache.has_key(queryString):
	    rsp_cache_hits += 1
	    return rsp_cache[queryString]
    else:
	    rsp_cache_misses += 1

    # make sure mailbox is selected
    log_imap("SEARCH query: '"+queryString+"'")
    start = time.time()
    try:
	imap.lock.acquire()
        resp, msgids_list = imap.uid("SEARCH", None, queryString)
	imap.lock.release()
    except:
	log_error("IMAP error on SEARCH")
	log_error("queryString: ->%s<-" % (queryString))
	print "\nIMAP exception ", sys.exc_info()[0]
    	exit(-1)
    log_imap_time("SEARCH", start);
    msgids = msgids_list[0].split(" ")
    log_imap2("search resp: %s msgids len: %d" % (resp, len(msgids)))
    ret = []
    for msgid in msgids:
        log_debug2("IMAP search result msg_uid: '%s'" % str(msgid))
	if len(str(msgid)) > 0:
            ret = msgids
	    break
    if len(rsp_cache) > 1000:
	clear_rsp_cache()
    rsp_cache[queryString] = ret
    return ret

def getSingleMsguidByQuery(imap, q):
        msgids = _getMsguidsByQuery("fillme1", imap, q)
	nr = len(msgids)
        if nr != 1:
	  qstr = string.join(q, " ")
	  # this is debug because it's normal to have non-existent files
          log_debug2("could not find messages for query: '%s' (found %d)" % (qstr, nr))
          return -1;
 	log_debug2("getSingleMsguidByQuery('%s') ret: '%s' nr: %d" % (string.join(q," "), msgids[0], nr))
	return int(msgids[0])

def __fetch_full_messages(imap, msgids):
	if msgids == None or len(msgids) == 0:
		return None
	data = __uid_cmd(imap, "FETCH", msgids, '(RFC822)')
	if data == None:
		return None
	log_imap("fetch(msgids=%s): got %d messages" % (string.join(msgids, ","), len(data)))
	#log_debug2("fetch msgid: '%s' resp: '%s' data: %d bytes" % (str(msgid), resp, len(data)))
	ret = {}
	for uid, raw_str in data.items():
		msg = email.message_from_string(raw_str)
		msg.uid = uid
		ret[str(uid)] = msg
        return ret

msg_cache = {}
def fetch_full_messages(imap, msgids):
	global msg_cache
	ret = {}
	fetch_msgids = []
	# if we do not hold the lock over this entire
	# sequence, we can race and fetch messages
	# twice.  It doesn't hurt, but it is inefficient
	hits = 0
	misses = 0
	imap.lock.acquire()
	for msgid in msgids:
		if msgid in msg_cache:
			ret[msgid] = msg_cache[msgid]
			hits += 1
		else:
			fetch_msgids.append(msgid)
			misses += 1
	log_debug3("fetch_full_messages() trying to fetch %d msgs" % (len(fetch_msgids)))
	fetched = None
	if len(fetch_msgids):
		fetched = __fetch_full_messages(imap, fetch_msgids)
	if fetched != None:
		ret.update(fetched)
		for uid, msg in fetched.items():
			if msg_cache.has_key(uid):
				print "uh oh, double-fetched uid: '%s'" % (uid)
			log_debug2("filled msg_cache[%s]" % (str(uid)))
			msg_cache[uid] = msg
	if len(msg_cache) > 1000:
		log_info("flushed message cache")
		msg_cache = {}
	imap.lock.release()
	log_debug3("fetch_full_messages() hits: %d misses: %d" % (hits, misses))
	return ret

def fetch_full_message(imap, msgid):
	resp = fetch_full_messages(imap, [str(msgid)])
	return resp[str(msgid)]
 
def getSingleMessageByQuery(desc, imap, q):
	log_debug2("getSingleMessageByQuery(%s)" % (desc))
	msgid = getSingleMsguidByQuery(imap, q)
	if msgid == -1:
		log_debug2("getSingleMessageByQuery() msgid: %s" % (str(msgid)))
		return None
	return fetch_full_message(imap, msgid)

def _pathSeparatorEncode(path):
    s1 = re.sub("/","__fs__",path)
    s2 = re.sub("-","__mi__",s1)
    return re.sub("\+","__pl__",s2)

def _pathSeparatorDecode(path):
    s1 = re.sub("__fs__","/",path)
    s2 = re.sub("__mi__","-",s1)
    return re.sub("__pl__","+",s2)


def _logException(msg):
    traceback.print_exc(file=sys.stderr)
    log.exception(msg)
    log.info(msg)

# Maybe I'm retarded, but I couldn't get this to work
# with python inheritance.  Oh, well.
def write_out_nolock(o, desc):
	if not o.dirty():
		log_debug2("object is not dirty, not writing out")
		return 0
	if isinstance(o, GmailInode):
		ret = o.i_write_out(desc)
	if isinstance(o, GmailDirent):
		ret = o.d_write_out(desc)
	if isinstance(o, OpenGmailFile):
		ret = o.f_write_out(desc)
	cleared = "none"
	if ret == 0:
		cleared = o.clear_dirty()
	log_debug1("write_out() finished '%s' (cleared '%s')" % (desc, cleared))
	return ret

def write_out(o, desc):
	if not o.writeout_lock.acquire():
		log_debug1("unable to get inode lock (%s)" % (desc))
		# someone else is writing this out
		return -2
	ret = write_out_nolock(o, desc)
	o.writeout_lock.release()
	return ret

class Dirtyable(object):
	def __init__(self):
		log_debug3("Dirtyable.__init__() '%s'" % (self))
	        self.__dirty = ""
		self.writeout_lock = thread.allocate_lock()

	def dirty(self):
    		return (len(self.__dirty) != 0)

	def dirty_reason(self):
    		return self.__dirty

	def clear_dirty(self):
    		cleared = self.__dirty
		self.__dirty = ""
		return cleared

	def mark_dirty(self, desc):
		log_debug1("mark_dirty('%s') because '%s'" % (self.to_str(), desc))
		self.writeout_lock.acquire()
		if len(self.__dirty) == 0:
			self.fs.dirty_objects.put(self)
		else:
			log_debug1("already in queue: mark_dirty('%s') because '%s'" % (self.to_str(), desc))
		self.__dirty = desc
		self.writeout_lock.release()

	def to_str(self):
		return "Dirtyable.to_str()"
# end class Dirtyable

#@+node:class GmailDirent
class GmailDirent(Dirtyable):
	def __init__(self, dirent_msg, inode, fs):
        	Dirtyable.__init__(self)
		self.dirent_msg = dirent_msg
		self.inode = inode
		self.fs = fs

	def to_str(self):
		return "dirent('%s' ino=%s)" % (self.path(), str(self.inode.ino))

	def path(self):
		d = self.fs.parse_dirent_msg(self.dirent_msg)
		file = _pathSeparatorDecode(d[FileNameTag])
		path = _pathSeparatorDecode(d[PathNameTag])
		log_debug3("decoded path: '%s' file: '%s'" % (path, file))
		log_debug3("subject was: ->%s<-" % (self.dirent_msg['Subject']))
		# path doesn't have a trailing slash, but the root
		# does have one.  Need to add one when we're dealing
		# with the non-root dir
		if path != "/":
			path += "/"
		return ("%s%s" % (path, file))

	def d_write_out(self, desc):
		log_info("writing out dirent '%s' for '%s' (dirty reason: '%s')"
				% (self.path(), desc, Dirtyable.dirty_reason(self)))
		imap = self.fs.get_imap()
		msgid = imap_append("dirent writeout", imap, self.dirent_msg)
		self.fs.put_imap(imap)
		if msgid <= 0:
		    e = OSError("Could not send mesg in write_out() for: '%s'" % (path))
	            e.errno = ENOSPC
       		    raise e
		return 0

	def unlink(self):
		# FIXME, don't allow directory unlinking when children
		log_debug1("unlink path:"+self.path()+" with nlinks:"+str(self.inode.i_nlink))
		if self.inode.mode & S_IFDIR:
			log_debug("unlinking dir")
			# guaranteed not to return any messages to
			# trash since there are two links for dirs
			self.inode.dec_nlink()
		else:
			log_debug("unlinking file")

		to_trash = self.inode.dec_nlink()
		to_trash.append(str(self.dirent_msg.uid))
		if len(to_trash):
			imap_trash_uids(self.fs.imap, to_trash)
		deleted = self.fs.dirent_cache.pop(self.path())
		if deleted != None and deleted != self:
			log_error("removed wrong dirent from cache")


#@-node:class GmailDirent

last_ino = -1

# using time for ino is a bad idea FIXME
#
# This helps, but there's still a theoretical
# problem if we mount(), write(), unmount()
# and mount again all within a second.
#
# Should we store this persistently in the
# root inode perhaps?
#
def get_ino():
    global last_ino
    ret = int(time.time()) << 16
    if ret <= last_ino:
	    ret = last_ino + 1
    return int(ret)

#@+node:class GmailInode
class GmailInode(Dirtyable):

    """
    Class used to store gmailfs inode details
    """
    #@+node:__init__
    def __init__(self, inode_msg, fs):
        Dirtyable.__init__(self)
	# We can either make this inode from scratch, or
	# use the inode_msg to fill in all these fields
	self.fs = fs
	self.xattr = {}
	self.inode_cache_lock = thread.allocate_lock()
	# protected by fs.inode_cache_lock
        self.pinned = 0
        if inode_msg != None:
 	    self.inode_msg = inode_msg
            self.fill_from_inode_msg()
	else:
            self.version = 2
            self.ino = get_ino()
            self.mode = 0
            self.dev = 0
            self.i_nlink = 0
            self.uid = 0
            self.gid = 0
            self.size = 0
            self.atime = 0
            self.mtime = 0
            self.ctime = 0
            self.symlink_tgt = ""
            self.blocksize = DefaultBlockSize
	    # there are a couple of spots that depend
	    # on having one of these around
	    self.inode_msg = self.mk_inode_msg()
    #@-node:__init__
    def to_str(self):
	    return "inode(%s)" % (str(self.ino))

    def mark_dirty(self, desc):
	log_debug2("inode mark_dirty(%s) size: '%s'" % (desc, str(self.size)))
        self.mtime = int(time.time())
	Dirtyable.mark_dirty(self, desc)

    def i_write_out(self, desc):
	log_debug2("i_write_out() self: '%s'" % (self))
	log_info("writing out inode for '%s' (dirty reason: '%s')" % (desc, Dirtyable.dirty_reason(self)))
	for attr in self.xattr:
		value = self.xattr[attr]
		payload_name = 'xattr-'+attr
		log_debug1("adding xattr payload named '%s': '%s'" % (payload_name, value))
		msg_add_payload(msg, value, payload_name)
	# remember where this is in case we have to delete it
	i_orig_uid = self.inode_msg.uid
	# because this wipes it out
	self.inode_msg = self.mk_inode_msg()
	imap = self.fs.get_imap()
	i_msgid = imap_append("inode writeout", imap, self.inode_msg)
	self.fs.put_imap(imap)
	if i_msgid > 0 and i_orig_uid > 0:
		log_debug("trashing old inode uid: %s new is: %s" % (i_orig_uid, i_msgid))
		imap_trash_uids(imap, [str(i_orig_uid)])
    	if i_msgid <= 0:
            e = OSError("Unable to write new inode message: '%s'" % (self.inode_msg['Subject']))
            e.errno = ENOSPC
            raise e
    	# Uh oh.  Does this properly truncate data blocks that are no
	# longer in use?
	return 0

    def fill_xattrs(self):
	log_debug3("fill_xattrs()")
	for part in self.inode_msg.get_payload():
		log_debug3("fill_xattrs() loop")
		fname = part.get_filename(None)
		log_debug3("fill_xattrs() fname: '%s'" % (str(fname)))
		if fname == None:
			continue
		m = re.match('xattr-(.*)', fname)
		if m == None:
			continue
		xattr_name = m.group(1)
		log_debug3("fill_xattrs() xattr_name: '%s'" % (xattr_name))
		self.xattr[xattr_name] = part.get_payload(decode=True)

    def mk_inode_msg(self):
   	dev = "11"
        subject = (InodeSubjectPrefix+ " " +
	    	   VersionTag     + "=" + GMAILFS_VERSION+ " " +
                   InodeTag       + "=" + str(self.ino)+ " " +
	           DevTag         + "=" + dev + " " +
		   NumberLinksTag + "=" + str(self.i_nlink)+ " " +
		   FsNameTag      + "=" + MagicStartDelim + fsNameVar +MagicEndDelim +
		   "")
        timeString = str(self.mtime)
	bsize = str(DefaultBlockSize)
	symlink_str = ""
	if self.symlink_tgt != None:
		symlink_str = _pathSeparatorEncode(self.symlink_tgt)
        body = (ModeTag  + "=" + str(self.mode)   + " " +
	        UidTag   + "=" + str(os.getuid()) + " " +
		GidTag   + "=" + str(os.getgid()) + " " +
		SizeTag  + "=" + str(self.size)   + " " +
		AtimeTag + "=" + timeString 	  + " " +
		MtimeTag + "=" + timeString 	  + " " +
		CtimeTag + "=" + timeString 	  + " " +
		BSizeTag + "=" + bsize            + " " +
		SymlinkTag+"=" + LinkStartDelim  + symlink_str + LinkEndDelim +
		"")
	return mkmsg(subject, body)

#yy		  SymlinkTag  + "=" + LinkStartDelim  + str + LinkEndDelim + " " +
#		ret[LinkToTag]   =     m.group(4)
#	link_to  = src_msg_hash[LinkToTag]
    def dec_nlink(self):
	self.i_nlink -= 1
	if self.i_nlink >= 1:
		self.mark_dirty("dec nlink")
		return []
	log_debug2("truncating inode")
	subject = 'b='+str(self.ino)+''
	block_uids = _getMsguidsByQuery("unlink blocks", self.fs.imap, [subject])
	to_trash = []
	to_trash.extend(block_uids)
	to_trash.append(str(self.inode_msg.uid))
	return to_trash

    def fill_from_inode_msg(self):
        """
        Setup the inode instances members from the gmail inode message
        """
	log_debug2("filling inode")
	if self.inode_msg.is_multipart():
		body = self.inode_msg.preamble
		log_debug2("message was multipart, reading body from preamble")
	else:
		# this is a bug
		log_debug2("message was single part")
        log_debug2("body: ->%s<-" % body)
	body = fixQuotedPrintable(body)
	##
	subj_hash = self.fs.parse_inode_msg_subj(self.inode_msg)
        self.version = subj_hash[VersionTag]
        self.ino = int(subj_hash[InodeTag])
	log_debug2("set self.ino to: int: '%d' str: '%s'" % (self.ino, str(subj_hash[InodeTag])))
        self.dev =     subj_hash[DevTag]
        self.i_nlink =   subj_hash[NumberLinksTag]
        #quotedEquals = "=(?:3D)?(.*)"
        quotedEquals = "=(.*)"
	restr = (	  ModeTag  + quotedEquals + ' ' +
			  UidTag   + quotedEquals + ' ' +
	  		  GidTag   + quotedEquals + ' ' +
	                  SizeTag  + quotedEquals + ' ' +
			  AtimeTag + quotedEquals + ' ' +
			  MtimeTag + quotedEquals + ' ' +
	                  CtimeTag + quotedEquals + ' ' +
	                  BSizeTag + quotedEquals + ' ' +
			  SymlinkTag + "=" + LinkStartDelim  + '(.*)' + LinkEndDelim)
        log_debug2("restr: ->%s<-" % (restr))
	m = re.search(re.compile(restr, re.DOTALL), body)
	self.mode  = int(m.group(1))
        self.uid   = int(m.group(2))
        self.gid   = int(m.group(3))
        self.size  = int(m.group(4))
        self.atime = int(m.group(5))
        self.mtime = int(m.group(6))
        self.ctime = int(m.group(7))
        self.blocksize = int(m.group(8))
	symlink_tmp    = m.group(9)
	self.symlink_tgt = _pathSeparatorDecode(symlink_tmp)
	log_debug2("filled inode size: %d" % self.size)
	self.fill_xattrs()

#@-node:class GmailInode

#@+node:class OpenGmailFile
class OpenGmailFile(Dirtyable):
    """
    Class holding any currently open files, includes cached instance of the last data block retrieved
    """
    
    def __init__(self, inode):
        Dirtyable.__init__(self)
        self.inode = inode
	self.fs = self.inode.fs
        self.tmpfile = None
        self.blocksRead = 0

        self.blocksize = inode.blocksize
        self.buffer = list(" "*self.blocksize)
        self.currentOffset = -1
        self.lastBlock = 0
        self.lastBlockRead = -1
        self.lastBlockBuffer = []
	self.users = 1
    def to_str(self):
	return "OpenGmailFile"

    def close(self):
        """
        Closes this file by committing any changes to the users gmail account
        """
	self.users -= 1
	if self.users >= 1:
	   return self.users
	return 0


    def write(self,buf,off):
        """
        Write data to file from buf, offset by off bytes into the file
        """
	log_debug2("write buf: '%s' off: %d self.currentOffset: %d\n" % (buf, off, self.currentOffset))
        buflen = len(buf)
        towrite = buflen

        if self.currentOffset == -1 or off<self.currentOffset or off>self.currentOffset:
            log_debug1("beginning new write")
            write_out(self, "begin new write")
            log_debug1("beginning new write done")
            self.currentOffset = off;
            self.buffer = self.readFromGmail(self.currentOffset/self.blocksize,1)

        currentBlock = self.currentOffset/self.blocksize
        written = 0
        while towrite>0:
            thiswrote = min(towrite,min(self.blocksize-(self.currentOffset%self.blocksize),self.blocksize))
            log_debug1("wrote %d bytes at offset: %d self.currentOffset: %d" % (thiswrote, off, self.currentOffset))
            self.buffer[self.currentOffset%self.blocksize:] = buf[written:written+thiswrote]
            towrite -= thiswrote
            written += thiswrote
            self.currentOffset += thiswrote
            self.lastBlock = currentBlock
	    log_debug1("write() setting dirty")
	    self.mark_dirty("file write")
	    self.inode.mark_dirty("file write")
            if self.currentOffset / self.blocksize > currentBlock:
                write_out(self, "changing block")
                currentBlock += 1
                if towrite > 0:
                    self.buffer = self.readFromGmail(currentBlock,1)

        if off + buflen > self.inode.size:
            self.inode.size = off + buflen
	self.inode.mark_dirty("file write extend")
        return buflen

    def f_write_out(self, desc):
        log_debug1("f_write_out() self.dirty: '%s' desc: '%s'" % (Dirtyable.dirty_reason(self), desc))

    	#a = self.inode.ga
        subject = ('b='+str(self.inode.ino)+
	          ' x='+str(self.lastBlock)+
		  ' '+FsNameTag+'='+MagicStartDelim+ fsNameVar +MagicEndDelim )
	tmpf = tempfile.NamedTemporaryFile()

        arr = array.array('c')
        arr.fromlist(self.buffer)
	log_debug("wrote contents to tmp file: ->"+arr.tostring()+"<-")

	tmpf.write(arr.tostring())
	tmpf.flush()

	msg = mkmsg(subject, fsNameVar, arr.tostring())
	imap = self.fs.get_imap()
	msgid = imap_append("commit data blocks (%d bytes)" % len(str(msg)), self.inode.fs.imap, msg)
	self.fs.put_imap(imap)
	log_debug("f_write_out() finished, rsp: '%s'" % str(msgid))
	if msgid > 0:
            log_debug("Sent write commit ok")
            self.inode.mark_dirty("commit data block")
	    tmpf.close()
            ret = 0
        else:
            log.error("Sent write commit failed")
	    tmpf.close()
            ret = -3
	return ret

    def read(self,readlen,offset):
        """
        Read readlen bytes from an open file from position offset bytes into the files data
        """
        
        readlen = min(self.inode.size-offset,readlen)
        outbuf = list(" "*readlen)
        toread = readlen;
        upto = 0;
        while toread>0:
           readoffset = (offset+upto)%self.blocksize
           thisread = min(toread,min(self.blocksize-(readoffset%self.blocksize),self.blocksize))
           outbuf[upto:] = self.readFromGmail((offset+upto)/self.blocksize,0)[readoffset:readoffset+thisread]
           upto+=thisread
           toread-=thisread
	   log_debug2("still to read: "+str(toread)+" upto now: " + str(upto))
	log_debug3("joined outbuf: ->%s<-" % string.join(outbuf, ""))
        return outbuf

    def readFromGmail(self,readblock,deleteAfter):
        """
        Read data block with block number 'readblock' for this file from users gmail account, if 'deleteAfter' is
        true then the block will be removed from Gmail after reading
        """

        log_debug2("readFromGmail() about to try and find inode:"+str(self.inode.ino)+" blocknumber:"+str(readblock))
        if self.lastBlockRead == readblock:
	    log_info("hit self.lastBlockRead cache (block %s)" % (readblock))
            contentList = list(" "*self.blocksize)
	    contentList[0:] = self.lastBlockBuffer
            return contentList
        q1 = 'b='+str(self.inode.ino)
	q2 = 'x='+str(readblock)
        msg = getSingleMessageByQuery("block read", self.inode.fs.imap, [ q1, q2 ])
	if msg == None:
	    log_debug2("readFromGmail(): file has no blocks, returning empty contents (%s %s)" % (q1, q2))
	    return list(" "*self.blocksize)
        log_debug2("got msg with subject:"+msg['Subject'])
	for part in msg.walk():
            log_debug2("message part.get_content_maintype(): '%s'" % part.get_content_maintype())
            if part.get_content_maintype() == 'multipart':
                continue
	    #if part.get('Content-Disposition') is None:
	    #    continue
	    log_debug2("message is multipart")
	    a = part.get_payload(decode = True)
	    log_debug3("part payload has len: %d asstr: '%s'" % (len(a), str(a)))
	log_debug3("after loop, a: '%s'" % str(a))
	a = list(a)

        if deleteAfter:
            imap_trash_msg(self.inode.fs.imap, msg)
        self.lastBlockRead = readblock
        self.lastBlockBuffer = a
        contentList = list(" "*self.blocksize)
        contentList[0:] = a
        return contentList

#@-node:class OpenGmailFile

#@+node:class Gmailfs
class Gmailfs(Fuse):

    #@	@+others
    def connect_to_server(self):
        global fsNameVar
        global password
        global username

	fsNameVar = DefaultFsname
        password = DefaultPassword
        username = DefaultUsername
        imap = imaplib.IMAP4_SSL("imap.gmail.com", 993);#libgmail.GmailAccount(username, password)
        if username.find("@")<0:
            username = username+"@gmail.com"
        imap.login(username, password)
	resp, data = imap.select(fsNameVar)
	#log_debug1("folder select '%s' resp: '%s' data: '%s'" % (fsNameVar, resp, data))
	if resp == "NO":
		#log_info("creating mailbox")
		resp, data = imap.create(fsNameVar)
		#log_debug1("create '%s' resp: '%s' data: '%s'" % (fsNameVar, resp, data))
		resp, data = imap.select(fsNameVar)
		#log_debug1("select2 '%s' resp: '%s' data: '%s'" % (fsNameVar, resp, data))
		return
	imap.lock = threading.Semaphore(1)
	return imap

    def get_imap(self):
	return self.imap_pool.get()

    def put_imap(self, imap):
	self.imap_pool.put(imap)

    #@+node:__init__
    def __init__(self, extraOpts, mountpoint, *args, **kw):
        Fuse.__init__(self, *args, **kw)

    	self.nr_imap_threads = 3
	self.imap_pool = Queue.Queue(self.nr_imap_threads)
	for i in range(self.nr_imap_threads):
		self.imap_pool.put(self.connect_to_server())

	self.dirty_objects = Queue.Queue(50)
	self.lookup_lock = threading.Semaphore(1)
        self.inode_cache_lock = threading.Semaphore(1)

        self.fuse_args.mountpoint = mountpoint
	self.fuse_args.setmod('foreground')
	self.optdict = extraOpts
        log_debug("Mountpoint: %s" % mountpoint)
	# obfuscate sensitive fields before logging
	#loggableOptdict = self.optdict.copy()
	#loggableOptdict['password'] = '*' * 8
	#log_info("Named mount options: %s" % (loggableOptdict,))

        # do stuff to set up your filesystem here, if you want

        self.openfiles = {}
        self.flush_dirent_cache()

        global DefaultBlockSize


#	options_required = 1
#	if self.optdict.has_key("reference"):
#	    try:
#		reference = References[self.optdict['reference']]
#		username = reference.username
#		password = reference.password
#		fsNameVar = reference.fsname
#	    except:
#		log.error("Invalid reference supplied. Using defaults.")
#	    else:
#		options_required = 0
#
#        if not self.optdict.has_key("username"):
#	    if options_required:
#	        log_warning('mount: warning, should mount with username=gmailuser option, using default')
#        else:
#            username = self.optdict['username']
#
#        if not self.optdict.has_key("password"):
#	    if options_required:
#        	log_warning('mount: warning, should mount with password=gmailpass option, using default')
#        else:
#            password = self.optdict['password']
#
#        if not self.optdict.has_key("fsname"):
#	    if options_required:
#        	log_warning('mount: warning, should mount with fsname=name option, using default')
#        else:
#            fsNameVar = self.optdict['fsname']
#
#        if self.optdict.has_key("blocksize"):
#            DefaultBlockSize = int(self.optdict['blocksize'])

#04:52.69 CAPABILITIES: ('IMAP4REV1', 'UNSELECT', 'IDLE', 'NAMESPACE', 'QUOTA', 'XLIST', 'CHILDREN', 'XYZZY')
#04:52.97 < * CAPABILITY IMAP4rev1 UNSELECT LITERAL+ IDLE NAMESPACE QUOTA ID XLIST CHILDREN X-GM-EXT-1 UIDPLUS COMPRESS=DEFLATE

	self.imap = self.connect_to_server()
	# This select() can be done read-only
	# might be useful for implementing "mount -o ro"
        log_info("Connected to gmail")
	#resp, data = self.imap.list()
	#log_info("list resp: " + resp)
	#for mbox in data:
	#	log_info("mbox: " + mbox)
	#log_info("done listing mboxes")

	#FIXME
	# we should probably make a mkfs command to
	# make the root inode.  We should probably
	# also make it search out and clear all
	# messages with the given label
	#self.imap.debug = 4
	trash_all = 0
	#trash_all = 1
	if trash_all:
		log_info("deleting existing messages...")
		self.imap.lock.acquire()
		resp, msgids = self.imap.uid("SEARCH", 'ALL')
		self.imap.lock.release()
		uids = msgids[0].split()
		log_info("%d found..." % (len(uids)))
		joined_uids = string.join(msgids[0].split(), ",")
		log_debug2("about to delete msgids: ->%s<-" % (joined_uids))
		if (len(uids)):
			imap_trash_uids(self.imap, uids)
		log_info("done deleting %d existing messages" % (len(msgids[0].split())))
		#exit(0)
	#elf.mythread()

        pass
    #@-node:__init__
    
    #@+node:attribs
    flags = 1

    #@-node:attribs

    class GmailStat(fuse.Stat):
        def __init__(self):
            self.st_mode = 0
            self.st_ino = 0
            self.st_dev = 0
            self.st_nlink = 0
            self.st_uid = 0
            self.st_gid = 0
            self.st_size = 0
            self.st_atime = 0
            self.st_mtime = 0
            self.st_ctime = 0
            self.st_blocks = 0
	    global IMAPBlockSize
            self.st_blksize = IMAPBlockSize
            self.st_rdev = 0

    #@+node:getattr
    def getattr(self, path):
        st = Gmailfs.GmailStat();
        log_debug2("getattr('%s')" % (path))
        #st_mode (protection bits)
        #st_ino (inode number)
        #st_dev (device)
        #st_nlink (number of hard links)
        #st_uid (user ID of owner)
        #st_gid (group ID of owner)
        #st_size (size of file, in bytes)
        #st_atime (time of most recent access)
        #st_mtime (time of most recent content modification)
        #st_ctime (time of most recent content modification or metadata change).

	log_debug3("getattr() -1")
        inode = self.lookup_inode(path)
	log_debug3("getattr() 0")
        if (inode == None) and (path == '/'):
		log_info("creating root inode")
		mode = S_IFDIR|S_IRUSR|S_IXUSR|S_IWUSR|S_IRGRP|S_IXGRP|S_IXOTH|S_IROTH
        	inode = self.mk_inode(mode, 1, 2)
		dirent = self.link_inode(path, inode)
		write_out(inode, "new root inode")
		write_out(dirent, "new root dirent")
		log_info("root inode uids: %s %s" % (dirent.dirent_msg.uid, inode.inode_msg.uid))
        	inode = self.lookup_inode(path)
		if inode == None:
			log_info("uh oh, can't find root inode")
			exit(-1)
	log_debug3("getattr() 1")

        if inode:
	    log_debug3("getattr() 2")
	    log_debug3("found inode for path: '%s'" % (path))
            st.st_mode  = inode.mode
            st.st_ino   = inode.ino
            st.st_dev   = inode.dev
            st.st_nlink = inode.i_nlink
            st.st_uid   = inode.uid
            st.st_gid   = inode.gid
            st.st_size  = inode.size
            st.st_atime = inode.atime
            st.st_mtime = inode.mtime
            st.st_ctme  = inode.ctime
            log_debug3("st.st_mode   = %d" % ( inode.mode))
            log_debug3("st.st_ino    = %d" % ( inode.ino))
            log_debug3("st.st_dev    = %d" % ( inode.dev))
            log_debug3("st.st_nlink  = %d" % ( inode.i_nlink))
            log_debug3("st.st_uid    = %d" % ( inode.uid))
            log_debug3("st.st_gid    = %d" % ( inode.gid))
            log_debug3("st.st_size   = %d" % ( inode.size))
            log_debug3("st.st_atime  = %d" % ( inode.atime))
            log_debug3("st.st_mtime  = %d" % ( inode.mtime))
            log_debug3("st.st_ctme   = %d" % ( inode.ctime))
	    log_debug3("getattr() 3: ->%s<-" % (str(st)))
            return st
    #else:
 	#log_info("getattr ENOENT: '%s'" % (path))
	    #e = OSError("No such file"+path)
	    #e.errno = ENOENT
	    #raise e
        log_debug3("getattr('%s') done" % (path))
	return -ENOENT
    #@-node:getattr

    #@+node:readlink
    def readlink(self, path):
        log_entry("readlink: path='%s'" % path)
        dirent = self.lookup_dirent(path)
	inode = dirent.inode
        if not (inode.mode & S_IFLNK):
            e = OSError("Not a link"+path)
            e.errno = EINVAL
            raise e
        log_debug("about to follow link in body:"+inode.msg.as_string())
	body = fixQuotedPrintable(inode.msg.as_string())
        m = re.search(SymlinkTag+'='+LinkStartDelim+'(.*)'+
                      LinkEndDelim,body)
        return m.group(1)
    #@-node:readlink

   #@+node:readdir
    def readdir(self, path, offset):
        log_entry("[%d] readdir('%s', %d)" % (thread.get_ident(), path, offset))
        log_debug3("at top of readdir");
        log_debug3("getting dir "+path)
        fspath = _pathSeparatorEncode(path)
        log_debug3("querying for:"+''+PathNameTag+'='+PathStartDelim+
                  fspath+PathEndDelim)
        # FIX need to check if directory exists and return error if it doesnt, actually
        # this may be done for us by fuse
	q = ''+PathNameTag+'='+PathStartDelim+fspath+PathEndDelim
        msgids = _getMsguidsByQuery("readdir", self.imap, [q])
        log_debug3("got readdir msg list")
        lst = []
        for dirlink in ".", "..":
            lst.append(dirlink)

	for c_path, inode in self.dirent_cache.items():
		c_dir, c_file = parse_path(c_path)
		if path != c_dir:
			continue
		# Found "." which we already have
		if len(c_file) == 0:
			continue
		log_debug2("found dir: '%s' file: '%s' for readdir('%s') in inode cache[%s]" % (c_dir, c_file, path, c_path))
		lst.append(c_file)
	for msgid, msg in fetch_full_messages(self.imap, msgids).items():
		subject = msg['Subject']
		#log_debug("thread.summary is " + thread.snippet)
		m = re.search(FileNameTag+'='+FileStartDelim+'(.*)'+
                           FileEndDelim, subject)
		if (m):
			# Match succeeded, we got the whole filename.
			log_debug("Used summary for filename")
			filename = m.group(1)

		log_debug("readdir('%s') found file: '%s'" % (path, filename))
		# this test for length is a special case hack for the root directory to prevent ls /gmail_root
		# returning "". This is hack is requried due to adding modifiable root directory as an afterthought, rather
		# than designed in at the start.
		if len(filename) <=0:
			continue
		filename = _pathSeparatorDecode(filename)
		if lst.count(filename) == 0:
			lst.append(filename)
	log_debug2("readdir('%s') got %d entries" % (path, len(lst)))
        for r in lst:
	    log_debug3("readdir('%s') entry: '%s'" % (path, r))
	    yield fuse.Direntry(r)
    #@-node:getdir

    dirent_cache = {}
    def flush_dirent_cache(self):
	    log_info("flush_dirent_cache()")
	    remove_keys = []
	    for path, dirent in self.dirent_cache.items():
		    log_debug3("dirent_cache[%s]: '%s'" % (path, str(dirent)))
		    if dirent.inode.dirty() or dirent.dirty():
			    continue
		    remove_keys.append(path)
	    for key in remove_keys:
		    dirent = self.dirent_cache[key]
		    del self.dirent_cache[key]
		    self.put_inode(dirent.inode)

	    while 1:
		try:
			# no args means do not block, and trow
			# exception immediately if empty
			object = self.fs.dirty_objects.get()
			write_out(object, "flush_dirent_cache()")
			log_info("flush_dirent_cache() wrote out %s" % (object.to_str()))
		except:
			log_info("no more object to flush")
			break
		size = self.fs.dirty_objects.qsize()
	    log_info("explicit flush done")

    #@+node:unlink
    def unlink(self, path):
        log_entry("unlink called on:"+path)
        try:
            dirent = self.lookup_dirent(path)
            dirent.unlink()
            return 0
        except:
            _logException("Error unlinking file"+path)
            e = OSError("Error unlinking file"+path)
            e.errno = EINVAL
            raise e
    #@-node:unlink

    #@+node:rmdir
    def rmdir(self, path):
        log_debug1("rmdir called on:"+path)
        #this is already checked before rmdir is even called
        #dirlist = self.getdir(path)
        #if len(dirlist)>0:
        #    e = OSError("directory not empty"+path)
        #    e.errno = ENOTEMPTY
        #    raise e
        dirent = self.lookup_dirent(path)
        dirent.unlink()

        # update number of links in parent directory
	parentdir, filename = parse_path(path)
        log_debug("about to rmdir with parentdir:"+parentdir)

        parentdirinode = self.lookup_inode(parentdir)
        parentdirinode.dec_nlink()
        return 0
        
    #@-node:rmdir
    
    #@+node:symlink
    def symlink(self, oldpath, newpath):
        log_debug1("symlink: oldpath='%s', newpath='%s'" % (oldpath, newpath))
	mode = S_IFLNK|S_IRWXU|S_IRWXG|S_IRWXO
	inode = self.mk_inode(mode, 0, 1)
	inode.symlink_tgt = newpath
	self.link_inode(oldpath, inode)

    #@-node:symlink

    # This provides a single, central place to define the format
    # of the message subjects.  'str' can be something like "%s"
    # to create a printf-style format string for output.  Or, it
    # can be a regex to help with input.
    def format_dirent_subj(self, str):
        # any change in here must be reflected in the two
	# functions below
        subject =(DirentSubjectPrefix+ " " +
		  PathNameTag + "=" + PathStartDelim  + str + PathEndDelim + " " +
		  FileNameTag + "=" + FileStartDelim  + str + FileEndDelim + " " +
                  RefInodeTag + "=" + str      	      + " " +
	          FsNameTag   + "=" + MagicStartDelim + str + MagicEndDelim+ " " +
		  VersionTag  + "=" + str)
	return subject

    def parse_dirent_msg(self, msg):
        subject_re = self.format_dirent_subj('(.*)')
	subject = msg['Subject'].replace("\r\n\t", " ")
        m = re.match(subject_re, subject)
	log_debug3("looking for regex: '%s'" % (subject_re))
	log_debug3("subject: '%s'" % (subject))
	log_debug3("match: '%s'" % (str(m)))
	ret = {}
	# Make sure these match the order of the strings in
	# format_dirent_subj()
	try:
		ret[PathNameTag] =     m.group(1)
 		ret[FileNameTag] =     m.group(2)
		ret[RefInodeTag] = int(m.group(3))
		ret[FsNameTag]   =     m.group(4)
		ret[VersionTag]  = int(m.group(5))
	except:
		log_error("unable to match regex\n\n\n\n")
		ret = None
	if ret[FsNameTag] != fsNameVar:
		log_error("msgid[%s] wrong filesystem: '%s'" % (msg.uid, ret[FsNameTag]))
		return None
	if ret[VersionTag] != int(GMAILFS_VERSION):
		log_error("msgid[%s] wrong version: '%s', expected '%d'" % (msg.uid, ret[VersionTag], int(GMAILFS_VERSION)))
		return None
	for key, val in ret.items():
		log_debug3("parse_dirent_msg() ret[%s]: '%s'" % (key, val))
	return ret;

    def mk_dirent_msg(self, path, inode_nr_ref):
	log_debug1("mk_dirent_msg('%s', 'ino=%s')" % (path, str(inode_nr_ref)))
	body = ""
	path, filename = parse_path(path)

	path = _pathSeparatorEncode(path)
	filename = _pathSeparatorEncode(filename)
	# again, make sure these are all in the correct order
	subject = self.format_dirent_subj("%s") % (
			path,
			filename,
			inode_nr_ref,
			fsNameVar,
			GMAILFS_VERSION)
	return mkmsg(subject, body)

    def parse_inode_msg_subj(self, inode_msg):
            subject = inode_msg['Subject'].replace('\u003d','=')
            log_debug3("parsing inode from subject:"+subject)
    	    ret = {}
            m = re.match((InodeSubjectPrefix+' '+
			  VersionTag+'=(.*) '+
			  InodeTag+'=(.*) '+
			  DevTag+'=(.*) '+
			  NumberLinksTag+'=(.*) '+
			  FsNameTag+'='+MagicStartDelim+'(.*)'+MagicEndDelim),
			 subject)
	    if m == None:
	    	return None
            ret[VersionTag]     = int(m.group(1))
	    ret[InodeTag]       = int(m.group(2))
	    ret[DevTag]         = int(m.group(3))
	    ret[NumberLinksTag] = int(m.group(4))
	    return ret


    #@+node:rename
    def rename(self, path_src, path_dst):
        log_debug1("rename from: '%s' -> '%s'" % (path_src, path_dst))
        src_dirent = self.lookup_dirent(path_src)
	if src_dirent == None:
		return -ENOENT

	dst_dirent = self.lookup_dirent(path_dst)
	if not dst_dirent == None:
		dst_dirent.unlink()
	# ensure the inode does not go away between
	# when we unlink and relink it
	inode = self.get_inode(src_dirent.inode.ino)
	# do the unlink first, because otherwise we
	# will get two dirents at the same path
	src_dirent.unlink()
	self.link_inode(path_dst, inode)
	self.put_inode(inode)

    #@-node:rename
    
    #@+node:link
    def link(self, old_path, new_path):
        log_entry("hard link: old_path='%s', new_path='%s'" % (old_path, new_path))
        inode = self.lookup_inode(old_path)
        if not (inode.mode & S_IFREG):
            e = OSError("hard links only supported for regular files not directories:"+oldpath)
            e.errno = EPERM
            raise e
        inode.mark_dirty("link")
	link_to(new_path, inode)
        return 0
    #@-node:link
    
    #@+node:chmod
    def chmod(self, path, mode):
        log_entry("chmod('%s', %o)" % (path, mode))
        inode = self.lookup_inode(path)
        inode.mode = (inode.mode & ~(S_ISUID|S_ISGID|S_ISVTX|S_IRWXU|S_IRWXG|S_IRWXO)) | mode
        inode.mark_dirty("chmod")
        return 0
    #@-node:chmod

    #@+node:chown
    def chown(self, path, user, group):
        log_entry("chown called with user:"+str(user)+" and group:"+str(group))
        inode = self.lookup_inode(path)
        inode.uid = user
        inode.gid = group
        inode.mark_dirty("chown")
        return 0
    #@-node:chown

    #@+node:truncate
    def truncate(self, path, size):
        inode = self.lookup_inode(path)
        log_entry("truncate '%s' to size: '%d' from '%d'" % (path, size, inode.size))
        # this is VERY lazy, we leave the truncated data around
        # it WILL be harvested when we grow the file again or
        # when we delete the file but should probably FIX
	if inode.size != size:
	        inode.size = size;
        	inode.mark_dirty("truncate")
        return 0
    #@-node:truncate

    #@+node:getxattr
    def getxattr(self, path, attr, size):
        log_entry("getxattr('%s', '%s', '%s')" % (path, attr, size))
        inode = self.lookup_inode(path)
	# TODO check to make sure we don't overflow size
	if attr not in inode.xattr:
		return -ENODATA
	ret = inode.xattr[attr]
	if size == 0:
		return len(ret)
        return ret
    #@-node:getxattr

    #@+node:setxattr
    def setxattr(self, path, attr, value, dunno):
        log_entry("setxattr('%s', '%s', '%s', '%s')" % (path, attr, value, dunno))
        inode = self.lookup_inode(path)
	inode.xattr[attr] = value
	inode.mark_dirty("setxattr")
    	return 0
    #@-node:setxattr

    #@+node:removexattr
    def removexattr(self, path, attr, value, dunno):
        log_entry("removexattr('%s', '%s')" % (path, attr))
        inode = self.lookup_dirent(path)/inode
	try:
		del inode.xattr[attr]
	except:
		return -ENOATTR
	inode.mark_dirty("removexattr")
    	return 0
    #@-node:removexattr

    #@+node:listxattr
    def listxattr(self, path, size):
        log_entry("listxattr('%s', '%s')" % (path, size))
        inode = self.lookup_inode(path)
	# We use the "user" namespace to please XFS utils
	attrs = []
	for attr in inode.xattr:
	        log_debug1("listxattr() attr: '%s'" % (attr))
		attrs.append(attr)
	if size == 0:
		# We are asked for size of the attr list, ie. joint size of attrs
		# plus null separators.
		return len("".join(aa)) + len(aa)
    	log_debug1("all attrs: (%s)" % (string.join(attrs, ", ")))
	return attrs
    #@-node:listxattr

    #@+node:mknod
    def mknod(self, path, mode, dev):
    	""" Python has no os.mknod, so we can only do some things """
        log_entry("mknod('%s')" % (path))
	if S_ISREG(mode) | S_ISFIFO(mode) | S_ISSOCK(mode):
	    inode = self.mk_inode(mode, 0, 1)
	    self.link_inode(path, inode)
	    # update parent dir??
    	    #open(path, "w")
    	else:
    		return -EINVAL
    #@-node:mknod

    def mk_dirent(self, inode, path):
	if self.dirent_cache.has_key(path):
		log_debug("dirent cache hit on path: '%s'" % (path))
		return self.dirent_cache[dirent.path()]
	# this should keep us from racing with lookup_dirent()
	self.lookup_lock.acquire()
	filename, dir = parse_path(path)
	msg = self.mk_dirent_msg(path, inode.ino)
	dirent = GmailDirent(msg, inode, self)
	dirent.mark_dirty("mk_dirent")
	if len(self.dirent_cache) > 1000:
                self.flush_dirent_cache()
	log_debug1("added dirent to cache for path: '%s'" % (dirent.path()))
        self.dirent_cache[dirent.path()] = dirent
	self.lookup_lock.release()
	return dirent

    def mk_inode(self, mode, size, nlink=1):
	inode = GmailInode(None, self)
	inode.mode = int(mode)
	inode.size = int(size)
	inode.i_nlink = int(nlink)
	inode.mark_dirty("new inode")
	self.inode_cache[inode.ino] = inode
	return inode

    def link_inode(self, path, inode):
	dirent = self.mk_dirent(inode, path)
	return dirent

    def lookup_inode(self, path):
    	dirent = self.lookup_dirent(path)
	if dirent == None:
		log_debug2("no dirent for path: '%s'" % (path))
		return None
	return dirent.inode

    #@+node:mkdir
    def mkdir(self, path, mode):
        log_entry("mkdir('%s', %o)" % (path, mode))
	if (self.lookup_dirent(path) != None):
		return -EEXIST
        inode = self.mk_inode(mode|S_IFDIR, 1, 2)
	self.link_inode(path, inode)
	parentdir, name = parse_path(path)
        parentdirinode = self.lookup_inode(parentdir)
        parentdirinode.i_nlink += 1
        parentdirinode.mark_dirty("mkdir")
    #@-node:mkdir

    #@+node:utime
    def utime(self, path, times):
        log_entry("utime for path:"+path+" times:"+str(times))
        inode = self.lookup_inode(path)
        inode.atime = times[0]
        inode.mtime = times[1]
        return 0
    #@-node:utime

    #@+node:open
    def open(self, path, flags):
        log_entry("gmailfs.py:Gmailfs:open: %s" % path)
        try:
            inode = self.lookup_inode(path)
	    # If the same file is opened twice, use the
	    # existing entry.  I'm not sure how
	    # semantically correct this is.  Seems like
	    # it could cause problems down the road.
	    # Who knows...
	    if self.openfiles.has_key(path):
	    	self.openfiles[path].users += 1
	    else:
		f = OpenGmailFile(inode)
		self.openfiles[path] = f
            return 0
        except:
	    _logException("Error opening file: "+path)
	    e = OSError("Error opening file: "+path)
            e.errno = EINVAL
            raise e
    #@-node:open

    #@+node:read
    def read(self, path, readlen, offset):
	log_entry("read")
        try:
 	    log_debug1("gmailfs.py:Gmailfs:read(len=%d, offset=%d, path='%s')" 
			    % (readlen, offset, path))
            f = self.openfiles[path]
            buf = f.read(readlen,offset)
            arr = array.array('c')
            arr.fromlist(buf)
            rets = arr.tostring()

            return rets
        except:
            _logException("Error reading file"+path)
            e = OSError("Error reading file"+path)
            e.errno = EINVAL
            raise e
    #@-node:read

    #@+node:write
    def write(self, path, buf, off):
	log_entry("write('%s', len:%d, off:%d)" % (path, len(buf), off))
        try:
            if log.isEnabledFor(logging.DEBUG):
                log_debug3("writing file contents: ->"+str(buf)+"<-")
            f = self.openfiles[path]
            written = f.write(buf,off)
	    log_debug2("wrote %d bytes to file: '%s'" % (written, f))
    	    return written
        except:
            _logException("Error opening file"+path)
            e = OSError("Error opening file"+path)
            e.errno = EINVAL
            raise e
    #@-node:write

    #@+node:release
    def release(self, path, flags):
        log_entry("gmailfs.py:Gmailfs:release: %s %x" % (path, int(flags)))
	# I saw a KeyError get thrown out of this once.  Looking back in
	# the logs, I saw two consecutive release:
	# 01/20/10 17:47:47 INFO       gmailfs.py:Gmailfs:release: /linux-2.6.git/.Makefile.swp 32768
	# 01/20/10 17:47:49 INFO       gmailfs.py:Gmailfs:release: /linux-2.6.git/.Makefile.swp 32769
	#
        f = self.openfiles[path]
	if f.close() == 0:
		#write_out(f, "release")
		# This write_out() is really slowing things down.
		#
		# Without it, there is a race:
		# 1. write() and queue file in dirty writeout queue for block write
		# 2. close(), and get in here
		# 3. remove file from openfiles[]
		# 4. new open(), and make a new OpenGmailFile created since
		#    openfiles[] no longer has an entry
		# 5. Write the same data block that is pending for write above...
		#    we won't find the first one
		#
		# Do we need to make a link from inode->data blocks waiting for
		# writeout?
		del self.openfiles[path]
        return 0
    #@-node:release

    def get_quota_info(self):
	# not really interesting because we don't care how much
	# is in the entire account, just our particular folder
	#resp, data = self.imap.getquota("")

	# response looks like:
	# [['"linux_fs_3" ""'], ['"" (STORAGE 368 217307895)']]
	# numbers are in 1k-sized blocks
	imap = self.get_imap()
	resp, data = imap.getquotaroot(fsNameVar)
	self.put_imap(imap)
	storage = data[1][0]
	m = re.match('"" \(STORAGE (.*) (.*)\)', storage)
	used_blocks = int(m.group(1))
	allowed_blocks = int(m.group(2))
	log_imap("quota resp: '%s'/'%s'" % (resp, data))
	return [used_blocks * 1024, allowed_blocks * 1024]


    #@+node:statfs
    def statfs(self):
	log_entry("statfs()")
        """
        Should return a tuple with the following 6 elements:
            - blocksize - size of file blocks, in bytes
            - totalblocks - total number of blocks in the filesystem
            - freeblocks - number of free blocks
            - availblocks - number of blocks available to non-superuser
            - totalfiles - total number of file inodes
            - freefiles - nunber of free file inodes

        Feel free to set any of the above values to 0, which tells
        the kernel that the info is not available.
        """
        st = fuse.StatVfs()
        block_size = 1024
        quotaBytesUsed, quotaBytesTotal = self.get_quota_info()
        blocks = quotaBytesTotal / block_size
        quotaPercent = 100.0 * quotaBytesUsed / quotaBytesTotal
        blocks_free = (quotaBytesTotal - quotaBytesUsed) / block_size
        blocks_avail = blocks_free # I guess...
        log_debug("%s of %s used. (%s)\n" % (quotaBytesUsed, quotaBytesTotal, quotaPercent))
        log_debug("Blocks: %s free, %s total\n" % (blocks_free, blocks))
        files = 0
        files_free = 0
        namelen = 80
        st.f_bsize = block_size
	st.f_frsize = block_size
	st.f_blocks = blocks
	st.f_bfree = blocks_free
	st.f_bavail = blocks_avail
	st.f_files = files
	st.f_ffree = files_free
	return st
    #@-node:statfs

    #@+node:fsync
    def fsync(self, path, isfsyncfile):
        log_entry("gmailfs.py:Gmailfs:fsync: path=%s, isfsyncfile=%s" % (path, isfsyncfile))
        log_info("gmailfs.py:Gmailfs:fsync: path=%s, isfsyncfile=%s" % (path, isfsyncfile))
        inode = self.lookup_inode(path)
        f = self.openfiles[path]
        write_out(f, "fsync")
	write_out(inode, "fsync")
        return 0
    #@-node:fsync

    #@+node:fsync
    def fsyncdir(self, path, isfsyncfile):
        log_entry("gmailfs.py:Gmailfs:fsyncdir: path=%s, isfsyncfile=%s" % (path, isfsyncfile))
        log_info("gmailfs.py:Gmailfs:fsyncdir: path=%s, isfsyncfile=%s" % (path, isfsyncfile))
        return -ENOSYS

    #@-node:fsync

    #@+node:fsync
    def flush(self, path):
        log_entry("gmailfs.py:Gmailfs:flush: path=%s" % (path))
        dirent = self.lookup_dirent(path)
	#write_out(dirent, "flush")
	#write_out(dirent.inode, "flush")
        return 0
    #@-node:fsync
   
    def fetch_dirent_msgs_for_path(self, dir_path):
	log_debug2("fetch_dirent_msgs_for_path('%s')" % (dir_path))
	encoded_path = _pathSeparatorEncode(dir_path)
	q = "" + PathNameTag + '=' + PathStartDelim + encoded_path + PathEndDelim
	about = ("dirent lookup('%s')" % (dir_path))
        dirent_msgids = _getMsguidsByQuery(about, self.imap, [q])
	log_debug2("q: '%s'" % (q))
	if len(dirent_msgids) == 0:
		log_debug2("could not find messages for path: '%s'" % (dir_path))
		return None
	log_debug2("fetch_dirent_msgs_for_path('%s') got back '%d' responses" % (dir_path, len(dirent_msgids)))
	return dirent_msgids

    def fetch_dirent_msg_for_path(self, path):
	if self.dirent_cache.has_key(path):
		return self.dirent_cache[path].dirent_msg
	else:
		log_debug2("fetch_dirent_msg_for_path('%s') missed the inode cache()" % (path))
		for path, inode in self.dirent_cache.items():
			log_debug3("in cache: '%s'" % (path))
	dirent_msgids = fetch_dirent_msg_for_path(dirpath)
	return dirent_msgids[0]

    inode_cache = {}
    inode_cache_lock = None
    def find_or_mk_inode(self, ino, msg):
	ino = int(ino)
	self.inode_cache_lock.acquire()
	if len(inode_cache) > 1000:
		log_info("flushing inode cache")
		new_inode_cache = {}
		for ino, inode in self.inode_cache:
			if inode.pinned < 1:
				continue
			new_inode_cache[ino] = inode
		self.inode_cache = new_inode_cache
	if self.inode_cache.has_key(ino):
		inode = self.inode_cache[ino]
	else:
	        inode = GmailInode(msg, self)
		self.inode_cache[ino] = inode
	self.inode_cache_lock.release()
	return inode

    def dirent_msg_iref(self, dirent_msg):
	dirent_msg_hash = self.parse_dirent_msg(dirent_msg)
	if dirent_msg_hash == None:
	    	log_debug1("lookup_dirent() failed to parse dirent_msg for uid '%s'" % (dirent_msg.uid))
		return None
       	return str(dirent_msg_hash[RefInodeTag])

    def get_inode(self, ino):
	ino = int(ino)
	self.inode_cache_lock.acquire()
	if not self.inode_cache.has_key(ino):
		self.inode_cache_lock.release()
		return None
	inode = self.inode_cache[ino]
	inode.pinned += 1
	self.inode_cache_lock.release()
	return inode

    def put_inode(self, inode):
	self.inode_cache_lock.acquire()
	inode.pinned -= 1
	self.inode_cache_lock.release()

    def mk_pinned_inode(self, msg):
	subj_hash = self.parse_inode_msg_subj(msg)
	ino = int(subj_hash[InodeTag])
        ret = None
	self.inode_cache_lock.acquire()
	if self.inode_cache.has_key(ino):
		ret = self.inode_cache[ino]
		log_debug2("pinned new inode nr: '%s'" % (str(ret.ino)))
	else:
		ret = GmailInode(msg, self)
		self.inode_cache[ret.ino] = ret
		log_debug2("pinned new inode nr: '%s'" % (str(ret.ino)))
	ret.pinned += 1
	self.inode_cache_lock.release()
	return ret

    def mk_pinned_inodes(self, msgs):
	inodes = []
	for uid, msg in msgs.items():
		inode = self.mk_pinned_inode(msg)
		inodes.append(inode)
	return inodes

    def mk_iref_query(self, dirent_msgs):
        query = []
        inodes = []
	dirent_msgs_by_iref = {}
	for uid, dirent_msg in dirent_msgs.items():
		iref = self.dirent_msg_iref(dirent_msg)
		dirent_msgs_by_iref[iref] = dirent_msg
		inode = self.get_inode(iref)
		if not inode == None:
			inodes.append(inode)
			continue
    		query.append(InodeTag+'='+iref)
	return dirent_msgs_by_iref, query, inodes

    def prefetch_dirent_msgs(self, dir):
	log_debug3("prefetch_dirent_msgs() 0")
    	dirent_msgids = self.fetch_dirent_msgs_for_path(dir)
        if dirent_msgids == None:
            return None

	log_debug2("prefetch_dirent_msgs('%s') going to fetch '%d' msgs" % (dir, len(dirent_msgids)))
    	dirent_msgs = fetch_full_messages(self.imap, dirent_msgids)
	log_debug1("prefetch_dirent_msgs('%s') got back '%d' msgs" % (dir, len(dirent_msgs)))

	dirent_msgs_by_iref, query, inodes = self.mk_iref_query(dirent_msgs)

	if len(query):
		inode_msguids = _getMsguidsByQuery("batch inode lookup", self.imap, query, 1)
		i_msgs = fetch_full_messages(self.imap, inode_msguids)
		inodes.extend(self.mk_pinned_inodes(i_msgs))

	log_debug3("prefetch_dirent_msgs() end")
	return dirent_msgs_by_iref

    def lookup_dirent(self, path):
	dir, filename = parse_path(path)
	# This cache checking is required at this point.  There
	# are inodes in the cache that have not been written to
	# storage, and will not show up when we do
	# self.fetch_dirent_msgs_for_path(), we must get them
	# from here.
        if self.dirent_cache.has_key(path):
            return self.dirent_cache[path]

	# We don't want to be simultaneously prefetching the same
	# messages in two different threads.  So, serialize the
	# lookups for now.
	self.lookup_lock.acquire()
	dirent_msgs_by_iref = self.prefetch_dirent_msgs(dir)
	if dirent_msgs_by_iref == None:
		self.lookup_lock.release()
		return None

        ret_dirent = None
	for iref, dirent_msg in dirent_msgs_by_iref.items():
		iref = int(iref)
		# no locking needed since we've already
		# pinned it
		if self.inode_cache.has_key(iref):
			inode = self.inode_cache[iref]
		else:
			log_error("dirent_msg (%s) refers to ino=%d which was not fetched" % (dirent_msg.uid, iref))
			log_error("dirent_msg subject: ->%s<-" % (dirent_msg['Subject']))
			continue
		new_dirent = GmailDirent(dirent_msg, inode, self)
		log_debug2("cached dirent: '%s'" % (new_dirent.path()))
	       	self.dirent_cache[new_dirent.path()] = new_dirent
		if new_dirent.path() == path:
			log_debug2("lookup_dirent() dirent: '%s'" % (new_dirent.path()))
			ret_dirent = new_dirent
	self.lookup_lock.release()
        return ret_dirent

    #@-others

#@-node:class Gmailfs
#@+node:mainline

# Setup logging
log = logging.getLogger('gmailfs')
#defaultLogLevel = logging.WARNING
defaultLogLevel = logging.DEBUG
log.setLevel(defaultLogLevel)
defaultLogFormatter = logging.Formatter("%(asctime)s %(levelname)-10s %(message)s", "%x %X")

# log to stdout while parsing the config while
defaultLoggingHandler = logging.StreamHandler(sys.stdout)
_addLoggingHandlerHelper(defaultLoggingHandler)

GmailConfig([SystemConfigFile,UserConfigFile])
try:
    libgmail.ConfigLogs(log)
except:
    pass

def main(mountpoint, namedOptions):
    log_debug1("Gmailfs: starting up, pid: %d" % (os.getpid()))
    global lead_thread
    lead_thread = thread.get_ident()
    if am_lead_thread():
	    print "am lead thread"
    else:
	    print "am NOT lead thread"
    server = Gmailfs(namedOptions,mountpoint,version="gmailfs 0.8.0",usage='',dash_s_do='setsingle')
    server.parser.mountpoint = mountpoint
    server.parse(errex=1)
    server.flags = 0
    #server.multithreaded = False;
    server.multithreaded = True;
    writeout_threads = []
    for i in range(server.nr_imap_threads):
	    t = testthread(server, i)
	    t.start()
	    writeout_threads.append(t)
    server.main()
    global do_writeout
    do_writeout = 0
    for t in writeout_threads:
	    print "joining thread..."
	    t.join()
	    print "done joining thread"
    log_info("unmount: flushing caches")
    server.flush_dirent_cache()
    imap_times_print(1)
    log_info("done")

if __name__ == '__main__':
    main(1, "2")
    
#@-node:mainline
#@-others
#@-node:@file gmailfs.py
#@-leo
