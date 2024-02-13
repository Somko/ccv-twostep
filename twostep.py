# -*- coding: utf-8 -*-
import argparse
import json
import logging
import serial
import serial.tools.list_ports
import sys
import traceback
from builtins import Exception
from cachetools import LRUCache
from flask import Flask, jsonify
from flask import current_app
from flask import make_response
from flask import request
from functools import reduce, wraps
from logging.handlers import SysLogHandler
from threading import Thread, Lock
from time import time, sleep

TWOSTEP_STX = bytes([0x02])  # Start of text
TWOSTEP_ETX = bytes([0x03])  # End of text
TWOSTEP_EOT = bytes([0x04])  # End of transmission
TWOSTEP_ENQ = bytes([0x05])  # Enquiry
TWOSTEP_ACK = bytes([0x06])  # Acknowledge
TWOSTEP_NAK = bytes([0x15])  # Neg Acknowledge

TWOSTEP_REQUEST = b'00C1'
TWOSTEP_RESPONSE = b'00D1'

VERIFONE_USB_VID = 0x11ca
VERIFONE_USB_PID = 0x0218

_logger = logging.getLogger(__name__)

tx_result_codes = {
    '-4': "Communication failure during TX: CHECK PAYMENT OK/NOK",
    '-3': "Communication failure: RETRY PAYMENT",
    '-2': "Transaction is running, check again",
    '-1': "Transaction not found",
    '0': "OK",
    '1': "Not OK",
    '2': "Valuta wrong",
    '3': "Productinfo wrong",
    '4': "Price/litre rate check failed",
    '5': "Total amount not equal to sum subtotals",
    '6': "Syntax Error, transaction failed",
    '7': "Amount not allowed (zero transaction)",
    '8': "Amount too high (> 99999,99)",
    '9': "Invalid Message Version Number",
    'A': "Trx still busy with (loyalty) transaction.",
}

issuer_result_codes = {
    '00': "no cardswipe (default)",
    '  ': "Bancontact/Mistercash",
    'EC': "MasterCard",
    'VI': "Visa / Visa Electron",
    'MX': "American Express",
    'DC': "Diners Club",
    'JC': "JCB card",
    'CC': "Comfort Card",
    'MA': "Maestro",
    'AU': "Aurora",
    'SE': "Sodexo e-Pass",
    'ER': "Edenred",
    'PF': "Payfair",
    'KD': "Kadoz",
    'RS': "RES",
    'CB': "Carte Bancaire",
    'VP': "V Pay",
    'BW': "Buy Way",
}

RESPONSE_ERR_TX_NOTFOUND = {
    "issuer_result_code": "00",
    "issuer_result_info": "no cardswipe (default)",
    "message_type": "0000",
    "tx_result_code": "-1",
    "tx_result_info": "Transaction not found"
}

RESPONSE_RUNNING = {
    u'issuer_result_code': u'00',
    u'issuer_result_info': u'no cardswipe (default)',
    u'message_type': u'0000',
    u'tx_result_code': u'-2',
    u'tx_result_info': u'Transaction is running, check again'
}

RESPONSE_ERR_NORESPONSE = {
    u'issuer_result_code': u'00',
    u'issuer_result_info': u'no cardswipe (default)',
    u'message_type': u'0000',
    u'tx_result_code': u'-3',
    u'tx_result_info': u'Communication failure: RETRY PAYMENT'
}

RESPONSE_ERR_TXERROR = {
    u'issuer_result_code': u'00',
    u'issuer_result_info': u'no cardswipe (default)',
    u'message_type': u'0000',
    u'tx_result_code': u'-4',
    u'tx_result_info': u'Communication failure during TX: CHECK PAYMENT OK/NOK'
}

RESPONSE_ERR_SYNTAX = {
    u'issuer_result_code': u'00',
    u'issuer_result_info': u'no cardswipe (default)',
    u'message_type': u'0000',
    u'tx_result_code': u'6',
    u'tx_result_info': u'Syntax Error, transaction failed'
}

RESPONSE_ERR_AMOUNTZERO = {
    u'issuer_result_code': u'00',
    u'issuer_result_info': u'no cardswipe (default)',
    u'message_type': u'0000',
    u'tx_result_code': u'7',
    u'tx_result_info': u'Amount not allowed (zero transaction)'
}

RESPONSE_ERR_AMOUNTHIGH = {
    u'issuer_result_code': u'00',
    u'issuer_result_info': u'no cardswipe (default)',
    u'message_type': u'0000',
    u'tx_result_code': u'8',
    u'tx_result_info': u'Amount too high (> 99999,99)'
}


class SerialPortNotFoundException(Exception):
    pass


class CCVTransactionStartException(Exception):

    def __init__(self, error):
        self.error_response = error


class TwoStepProtocolDriver(Thread):

    def __init__(self, serial_port=None, debug=False):
        self.device = None
        self.debug = debug
        self.serial_port = serial_port
        self.transaction_lock = Lock()
        self.transaction_busy = False
        self.transaction_results = LRUCache(maxsize=100)
        self.transaction_counter = 0
        self.request_retries = 4
        self.response_retries = 4
        self.ack_timeout = 3
        self.response_timeout = 10
        self.transaction_timeout = 240

        self.timeout_timestamp = False

    @staticmethod
    def find_port(debug=False):
        discovered_port = None

        for port in serial.tools.list_ports.comports():
            if port.pid == VERIFONE_USB_PID and port.vid == VERIFONE_USB_VID:
                discovered_port = port.device
                break

        if not discovered_port:
            for port in serial.tools.list_ports.comports():
                if 'usbserial' in port.device:
                    discovered_port = port.device
                    break
                elif 'ttyACM' in port.device:
                    discovered_port = port.device
                    break
                elif 'ttyUSB' in port.device:
                    discovered_port = port.device
                    break

        if debug and discovered_port:
            return 'spy://' + discovered_port
        elif discovered_port:
            return discovered_port
        else:
            raise SerialPortNotFoundException('No serial port found')

    def opendevice(self):
        if self.serial_port is None:
            serial_port = TwoStepProtocolDriver.find_port(debug=self.debug)
        else:
            serial_port = self.serial_port

        _logger.info('Opening port %s' % serial_port)
        self.device = serial.serial_for_url(
            url=serial_port,
            baudrate=9600,
            bytesize=7,
            parity=serial.PARITY_EVEN,
            stopbits=1,
        )

    def closedevice(self):
        if self.device is None:
            _logger.warning('Close device called and device is None')
        else:
            self.device.close()
            self.device = None

    def flush_input_from_terminal(self):
        _logger.debug('Flushing data from terminal starting')
        self.device.reset_input_buffer()
        sleep(.5)
        while self.device.in_waiting:
            self.device.reset_input_buffer()
            sleep(.5)

    def read_ack_from_terminal(self):
        _logger.debug('Reading ACK from terminal starting')
        bytes_read = b''
        ack_timeout_timestamp = time() + self.ack_timeout
        self.device.timeout = 1
        result = None
        while True:
            buffer = self.device.read(size=1)
            bytes_read += buffer
            _logger.debug('Reading ack - %s bytes from terminal' % bytes_read)
            if TWOSTEP_ACK in buffer:
                _logger.debug('GOT ACK byte from terminal')
                result = TWOSTEP_ACK
                break
            elif TWOSTEP_NAK in buffer:
                _logger.debug('GOT NAK byte from terminal')
                result = TWOSTEP_NAK
                break
            elif time() > ack_timeout_timestamp:
                _logger.debug('Timeout while reading ack from terminal')
                result = False
                break
        return result

    def read_from_terminal(self):
        _logger.debug('read_from_terminal starting')

        response_message = {}
        nack_retries = self.response_retries
        while nack_retries > 0:

            response = self.read_sigle_response()

            if TWOSTEP_STX in response and TWOSTEP_ETX in response:
                stx_idx = response.index(TWOSTEP_STX)
                etx_idx = response.index(TWOSTEP_ETX)
                if len(response) >= etx_idx + 1:
                    lcr_received = bytes(
                        response[etx_idx + 1:etx_idx + 2]
                    )
                else:
                    lcr_received = None
                # LCR is calculated over all data starting
                # after STX unto ETX included.
                calculated_lcr = self.calc_lcr(
                    response[stx_idx + 1:etx_idx + 1]
                )
                if lcr_received == calculated_lcr:
                    _logger.debug('Received message, LCR OK')
                    response_message = self.parse_transaction_response(
                        response[stx_idx:]
                    )
                    self.send_ack()
                    break
                else:
                    nack_retries -= 1
                    self.send_nak()
                    _logger.debug(
                        'Received message, LCR NOK - expected _%s_ got _%s_ '
                        '- retries left %s' %
                        (calculated_lcr, lcr_received, nack_retries)
                    )
                    response_message = RESPONSE_ERR_TXERROR
            elif len(response):
                _logger.debug(
                    'Received garbage, sending NAK: _%s_' % response
                )
                response_message = RESPONSE_ERR_TXERROR
                nack_retries -= 1
                self.send_nak()
            elif time() > self.timeout_timestamp:
                _logger.debug(
                    'Timeout waiting for transaction response'
                )
                response_message = RESPONSE_ERR_TXERROR
                break
            else:
                _logger.debug(
                    'No valid response yet from terminal: _%s_' % response
                )

        return response_message

    def read_sigle_response(self):
        _logger.debug('read_sigle_response starting')
        buffer = b''
        self.device.timeout = 1
        response_timeout_time = time() + self.response_timeout

        # set a maximum of bytes we want to read
        # if we receive ETX, we set this to 1 so we can finish after
        # reading the nex byte
        bytes_to_read = 512
        while bytes_to_read > 0:
            if time() > response_timeout_time:
                _logger.debug('Timeout while reading bytes from terminal')
                break

            byte_read = self.device.read(size=1)
            if byte_read != b'':
                buffer += byte_read
                bytes_to_read -= 1
            if byte_read == TWOSTEP_ETX:
                # received ETX, next byte should be the LCR
                bytes_to_read = 1
            elif not len(byte_read):
                _logger.debug(
                    'No data yet from terminal, still waiting for %s seconds' %
                    (response_timeout_time - time())
                )

            _logger.debug('Read %s bytes from terminal' % buffer)
        return buffer

    def start_transaction(self,
                          amount,
                          terminal_number=0,
                          product_info='',
                          receipt_number=1,
                          currency='EUR',
                          transaction_id=0):
        _logger.info(
            'Starting transaction for amount %s, id=%s' % (
                amount, transaction_id)
        )
        tx_message_has_been_sent = False
        if not self.transaction_lock.acquire(blocking=False):
            _logger.error(
                'Cannot acquire lock for transaction id=%s' % transaction_id
            )
            return False
        try:
            _logger.debug(
                'Transaction id=%s has acquired the lock' % transaction_id
            )
            self.transaction_busy = True
            self.opendevice()
            # Already update the result status, so the check_tx will not
            # return not found.
            self.transaction_results.update({
                transaction_id: RESPONSE_RUNNING
            })
            # Set transaction timeout
            self.timeout_timestamp = time() + self.transaction_timeout
            _logger.info('Sending request to terminal')
            self.flush_input_from_terminal()
            request_sent = self.send_request(
                amount,
                terminal_number=terminal_number,
                product_info=product_info,
                receipt_number=receipt_number,
                currency=currency)
            tx_message_has_been_sent = True
            if not request_sent:
                _logger.error('No response from terminal')
                self.transaction_results.update({
                    transaction_id: RESPONSE_ERR_NORESPONSE
                })
            else:
                _logger.info('Getting response from terminal')
                result = self.read_from_terminal()
                _logger.info('Updating response result from terminal')
                self.transaction_results.update({
                    transaction_id: result,
                })

                self.flush_input_from_terminal()
        except CCVTransactionStartException as ex:
            result = ex.error_response
            self.transaction_results.update({
                transaction_id: result,
            })
        except Exception as ex:
            _logger.exception('Exception during tx_id %s' % transaction_id)
            ex_type, ex_value, ex_traceback = sys.exc_info()
            if tx_message_has_been_sent:
                result = RESPONSE_ERR_TXERROR.copy()
            else:
                result = RESPONSE_ERR_NORESPONSE.copy()
            result.update({
                'err_status': "%s - %s" % (ex.__class__.__name__, ex),
                'err_info': traceback.format_exception(
                    ex_type, ex_value, ex_traceback),
            })
            self.transaction_results.update({
                transaction_id: result,
            })
        finally:
            _logger.info(
                'Transaction id=%s has released the lock' % transaction_id
            )
            self.closedevice()
            self.transaction_busy = False
            self.transaction_lock.release()

    def start_transaction_thread(self,
                                 amount,
                                 terminal_number=0,
                                 product_info='',
                                 receipt_number=1,
                                 currency='EUR'):
        self.transaction_counter += 1
        transaction_id = self.transaction_counter
        if self.transaction_busy:
            return False
        else:
            transaction_thread = Thread(
                target=self.start_transaction,
                kwargs={
                    'amount': amount,
                    'terminal_number': terminal_number,
                    'product_info': product_info,
                    'receipt_number': receipt_number,
                    'currency': currency,
                    'transaction_id': transaction_id
                }
            )
            transaction_thread.start()
            return transaction_id

    def check_status(self, transaction_id):
        return self.transaction_results.get(transaction_id)

    @staticmethod
    def calc_lcr(message):
        _logger.debug('Calculating LCR over _%s_' % message)
        return bytes([reduce(lambda lrc, byte: lrc ^ byte, message)])

    @staticmethod
    def transaction_request(amount=0,
                            terminal_number=0,
                            product_info='',
                            receipt_number=1,
                            currency='EUR'):
        message_format = (
            '%(terminal_number)08d'
            '%(message_version_number)01d'
            '%(amount)011d'
            '%(product_info).20s'
            '%(receipt_number)06d'
            '%(transaction_type)02d'
            '%(additional_info_len)03d'
            '%(additional_info_type)02d'
            '%(additional_info_data)s'
        )

        if not type(amount) in (int, float):
            raise CCVTransactionStartException(RESPONSE_ERR_SYNTAX)
        if not amount <= 99999.99:
            raise CCVTransactionStartException(RESPONSE_ERR_AMOUNTHIGH)
        if not amount >= 0.01:
            raise CCVTransactionStartException(RESPONSE_ERR_AMOUNTZERO)
        if not receipt_number <= 999999:
            raise CCVTransactionStartException(RESPONSE_ERR_SYNTAX)
        if not terminal_number <= 99999999:
            raise CCVTransactionStartException(RESPONSE_ERR_SYNTAX)

        message_data = {
            'terminal_number': terminal_number,
            'message_version_number': 1,
            'amount': amount * 100,
            'product_info': product_info,
            'receipt_number': receipt_number,
            'transaction_type': 0,
            'additional_info_len': 5,
            'additional_info_type': 1,
            'additional_info_data': currency,
        }

        transaction_message = (message_format % message_data).encode(
            encoding='ascii')

        transaction_lrc = TwoStepProtocolDriver.calc_lcr(
            TWOSTEP_REQUEST + transaction_message + TWOSTEP_ETX
        )

        complete_message = (
                TWOSTEP_STX +
                TWOSTEP_REQUEST +
                transaction_message +
                TWOSTEP_ETX +
                transaction_lrc
        )

        return complete_message

    def send_ack(self):
        self.device.write(TWOSTEP_ACK)
        self.device.flush()

    def send_nak(self):
        self.device.write(TWOSTEP_NAK)
        self.device.flush()

    def send_request(self,
                     amount,
                     terminal_number=0,
                     product_info='',
                     receipt_number=1,
                     currency='EUR'):
        tx_request = self.transaction_request(
            amount,
            terminal_number=terminal_number,
            product_info=product_info,
            receipt_number=receipt_number,
            currency=currency,
        )

        ack_received = False
        retries_left = self.request_retries
        while retries_left > 0:

            self.device.write(tx_request)
            self.device.flush()
            ack_received = self.read_ack_from_terminal()
            if ack_received == TWOSTEP_ACK:
                break
            elif ack_received == TWOSTEP_NAK:
                retries_left -= 1
                _logger.debug(
                    'send_request got NAK, %s retries left' % retries_left
                )
            elif not ack_received:
                _logger.debug(
                    'send_request got no ACK/NAK response, %s retries left' %
                    retries_left
                )
                retries_left -= 1

        return ack_received == TWOSTEP_ACK

    @staticmethod
    def parse_transaction_response(terminal_response):
        assert terminal_response[0:1] == TWOSTEP_STX
        message_type = terminal_response[1:5]
        assert message_type == TWOSTEP_RESPONSE

        terminal_number = int(terminal_response[5:13])
        response_amount = int(terminal_response[13:25]) / 100.0
        issuer_result_code = terminal_response[25:27].decode('ascii')
        tx_result_code = terminal_response[27:28].decode('ascii')

        issuer_result_info = issuer_result_codes.get(
            issuer_result_code, 'unknown')
        tx_result_info = tx_result_codes.get(
            tx_result_code, 'unknown')

        ret = {
            'message_type': message_type.decode('ascii'),
            'terminal_number': terminal_number,
            'response_amount': response_amount,
            'issuer_result_code': issuer_result_code,
            'tx_result_code': tx_result_code,
            'issuer_result_info': issuer_result_info,
            'tx_result_info': tx_result_info,
        }
        return ret


parser = argparse.ArgumentParser(description="CCV Twostep proxy.")
parser.add_argument(
    '--ssl-cert',
    help='Specify SSL Certificate file'
)
parser.add_argument(
    '--ssl-key',
    help='Specify SSL Key file'
)
parser.add_argument(
    '--port',
    help='Port number, defaults to 5000',
    type=int,
    default=5000,
)
parser.add_argument(
    '--debug',
    help='Debug mode',
    action='store_const',
    const=True,
)

options = parser.parse_args()

app = Flask(__name__)

root_logger = logging.getLogger()
root_logger.addHandler(logging.StreamHandler())
root_logger.addHandler(SysLogHandler(address='/dev/log'))
if options.debug:
    root_logger.setLevel(logging.DEBUG)
else:
    root_logger.setLevel(logging.INFO)

if all((options.ssl_cert, options.ssl_key)):
    _logger.info('Starting with SSL Enabled')
    ssl_mode = True
else:
    _logger.info('Starting with SSL Disabled')
    ssl_mode = False

driver = TwoStepProtocolDriver(debug=options.debug)


def add_response_headers(headers=None):
    """This decorator adds the headers passed in to the response"""

    if headers is None:
        headers = {}

    def decorator(f):
        @wraps(f)
        def decorated_function(*args, **kwargs):
            resp = make_response(f(*args, **kwargs))
            h = resp.headers
            for header, value in headers.items():
                h[header] = value
            return resp

        return decorated_function

    return decorator


def set_cors(f):
    return add_response_headers({
        'Access-Control-Allow-Origin': '*',
        'Access-Control-Allow-Methods': 'GET, POST',
        'Access-Control-Allow-Headers': 'Origin, Content-Type, X-Auth-Token',
    })(f)


def jsonp(func):
    """Wraps JSONified output for JSONP requests."""

    @wraps(func)
    def decorated_function(*args, **kwargs):
        result_data = func(*args, **kwargs)
        callback = request.args.get('callback', False)
        if callback:
            result = json.dumps(result_data)
            content = "%s(%s)" % (callback, result)
            mimetype = 'application/javascript'
            return current_app.response_class(content, mimetype=mimetype)
        else:
            return jsonify(result_data)

    return decorated_function


@app.route('/start_tx', methods=['GET'])
@set_cors
@jsonp
def start_tx():
    try:
        amount = float(request.args.get('amount', '0.0'))
    except:
        return {'err': 'Cannot parse amount', }

    tx_id = driver.start_transaction_thread(
        amount=amount,
        product_info=request.args.get('product_info', ''),
        currency=request.args.get('currency', 'EUR'),
    )

    if not tx_id:
        return {'err': 'Terminal is busy', }
    else:
        return {
            'status': 'Transaction started',
            'tx_id': tx_id,
        }


@app.route('/check_tx/<int:tx_id>', methods=['GET'])
@set_cors
@jsonp
def check_status(tx_id):
    result = driver.check_status(tx_id)

    if not result:
        return RESPONSE_ERR_TX_NOTFOUND
    else:
        return result


@app.route('/', methods=['GET'])
def home():
    return "Accomodata CCV BOX is up and running\n"


if __name__ == '__main__':
    if ssl_mode:
        app.run(
            host='0.0.0.0',
            port=options.port,
            ssl_context=(options.ssl_cert, options.ssl_key),
        )
    else:
        app.run(
            port=options.port,
            host='0.0.0.0',
        )