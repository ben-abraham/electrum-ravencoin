#!/usr/bin/env python
#
# Electrum - lightweight Bitcoin client
# Copyright (C) 2012 thomasv@gitorious
#
# Permission is hereby granted, free of charge, to any person
# obtaining a copy of this software and associated documentation files
# (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge,
# publish, distribute, sublicense, and/or sell copies of the Software,
# and to permit persons to whom the Software is furnished to do so,
# subject to the following conditions:
#
# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
# BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
# ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import re
import decimal, asyncio
import concurrent, concurrent.futures
from decimal import Decimal
from functools import partial
from typing import Optional, TYPE_CHECKING, Sequence, List, Union

from PyQt5.QtGui import QPixmap, QKeySequence, QIcon, QCursor, QFont, QRegExpValidator
from PyQt5.QtCore import Qt, QRect, QStringListModel, QSize, pyqtSignal, QPoint
from PyQt5.QtCore import QTimer, QRegExp
from PyQt5.QtWidgets import (QMessageBox, QComboBox, QSystemTrayIcon, QTabWidget,
                             QMenuBar, QFileDialog, QCheckBox, QLabel,
                             QVBoxLayout, QGridLayout, QLineEdit,
                             QHBoxLayout, QPushButton, QScrollArea, QTextEdit,
                             QShortcut, QMainWindow, QCompleter, QInputDialog,
                             QWidget, QSizePolicy, QStatusBar, QToolTip, QDialog,
                             QMenu, QAction, QStackedWidget, QToolButton, )

from electrum import ravencoin, assets
from electrum.ravencoin import COIN, is_address, base_decode, TOTAL_COIN_SUPPLY_LIMIT_IN_BTC
from electrum.i18n import _
from electrum.util import bfh, maybe_extract_bolt11_invoice, BITCOIN_BIP21_URI_SCHEME, Satoshis
from electrum.invoices import PR_TYPE_ONCHAIN, PR_TYPE_LN, PR_DEFAULT_EXPIRATION_WHEN_CREATING, Invoice
from electrum.invoices import PR_PAID, PR_FAILED, pr_expiration_values, LNInvoice, OnchainInvoice
from electrum.transaction import PartialTxOutput, RavenValue, PartialTransaction, Transaction, SwapTransaction
from electrum.ravencoin import opcodes, construct_script
from electrum.wallet import (Multisig_Wallet, CannotBumpFee, Abstract_Wallet,
                             sweep_preparations, InternalAddressCorruption,
                             CannotDoubleSpendTx, CannotCPFP)
from electrum.logging import Logger
from electrum.lnaddr import LnDecodeException

from .qrtextedit import ScanQRTextEdit
from .amountedit import AmountEdit, RVNAmountEdit, FreezableLineEdit, FeerateEdit, PayToAmountEdit
from .qrcodewidget import QRCodeWidget, QRDialog
from .qrtextedit import ShowQRTextEdit, ScanQRTextEdit
from .completion_text_edit import CompletionTextEdit
from . import util
from .util import (read_QIcon, ColorScheme, text_dialog, icon_path, WaitingDialog,
                   WindowModalDialog, ChoicesLayout, HelpLabel, Buttons,
                   OkButton, InfoButton, WWLabel, TaskThread, CancelButton,
                   CloseButton, HelpButton, MessageBoxMixin, EnterButton,
                   import_meta_gui, export_meta_gui,
                   filename_field, address_field, char_width_in_lineedit, webopen,
                   TRANSACTION_FILE_EXTENSION_FILTER_ANY, MONOSPACE_FONT,
                   getOpenFileName, getSaveFileName, BlockingWaitingDialog)
from .util import ButtonsTextEdit, ButtonsLineEdit, ComplexLineEdit

if TYPE_CHECKING:
    from .main_window import ElectrumWindow

class AtomicSwapExecute(QWidget, MessageBoxMixin):
  parsed_swap: SwapTransaction = None
  execute_swap_action = pyqtSignal(SwapTransaction)

  def __init__(self, parent, gui_object: 'ElectrumGui', wallet: Abstract_Wallet):
    super().__init__(parent)
    self.gui_object = gui_object
    self.config = gui_object.config
    self.app = gui_object.app
    self.wallet = wallet
    self.fx = False
    # A 4-column grid layout.  All the stretch is in the last column.
    # The exchange rate plugin adds a fiat widget in column 2
    self.receive_grid = grid = QGridLayout()
    grid.setSpacing(8)
    grid.setColumnStretch(3, 1)

    self.signed_partial_e = QTextEdit()
    grid.addWidget(QLabel(_('Signed Partial')), 0, 0)
    grid.addWidget(self.signed_partial_e, 0, 1, 1, 4)
    self.signed_partial_e.textChanged.connect(self.update_form)

    self.clear_swap_button = QPushButton(_('Clear'))
    self.clear_swap_button.clicked.connect(self.clear_swap)
    self.execute_swap_button = QPushButton(_('Execute'))
    self.execute_swap_button.setIcon(read_QIcon("ravencoin.png"))
    self.execute_swap_button.setToolTip('Complete and execute signed partial transaction.')
    self.execute_swap_button.clicked.connect(lambda: self.execute_swap(False))
    self.receive_buttons = buttons = QHBoxLayout()
    buttons.addStretch(1)
    buttons.addWidget(self.clear_swap_button)
    buttons.addWidget(self.execute_swap_button)
    self.rec_buttons_widget = QWidget()
    self.rec_buttons_widget.setLayout(buttons)
    #grid.addLayout(buttons, 4, 3, 1, 2)

    self.receive_payreq_e = ButtonsTextEdit()
    self.receive_payreq_e.setFont(QFont(MONOSPACE_FONT))
    self.receive_payreq_e.addCopyButton(self.app)
    self.receive_payreq_e.setReadOnly(True)
    self.receive_payreq_e.textChanged.connect(self.update_receive_qr)
    self.receive_payreq_e.setFocusPolicy(Qt.ClickFocus)

    self.receive_qr = QRCodeWidget(fixedSize=220)
    self.receive_qr.mouseReleaseEvent = lambda x: self.toggle_qr_window()
    self.receive_qr.enterEvent = lambda x: self.app.setOverrideCursor(QCursor(Qt.PointingHandCursor))
    self.receive_qr.leaveEvent = lambda x: self.app.setOverrideCursor(QCursor(Qt.ArrowCursor))

    self.receive_address_e = ButtonsTextEdit()
    self.receive_address_e.setFont(QFont(MONOSPACE_FONT))
    self.receive_address_e.addCopyButton(self.app)
    self.receive_address_e.setReadOnly(True)
    self.receive_address_e.textChanged.connect(self.update_receive_address_styling)

    qr_show = lambda: self.show_qrcode(str(self.receive_address_e.text()), _('Receiving address'), parent=self)
    qr_icon = "qrcode_white.png" if ColorScheme.dark_scheme else "qrcode.png"
    self.receive_address_e.addButton(qr_icon, qr_show, _("Show as QR code"))

    self.details_grid = d_grid = QGridLayout()
    d_grid.setSpacing(8)
    d_grid.setColumnStretch(3, 1)

    self.details_valid_l = QLabel()
    d_grid.addWidget(QLabel(_('Valid')), 0, 0)
    d_grid.addWidget(self.details_valid_l, 0, 1, 1, 4)

    self.details_order_type_l = QLabel()
    d_grid.addWidget(QLabel(_('Order Type')), 1, 0)
    d_grid.addWidget(self.details_order_type_l, 1, 1, 1, 4)

    self.details_asset_l = QLabel()
    d_grid.addWidget(QLabel(_('Asset')), 2, 0)
    d_grid.addWidget(self.details_asset_l, 2, 1, 1, 4)

    self.details_unit_price_l = QLabel()
    d_grid.addWidget(QLabel(_('Unit Price')), 3, 0)
    d_grid.addWidget(self.details_unit_price_l, 3, 1, 1, 4)

    self.details_total_price_l = QLabel()
    d_grid.addWidget(QLabel(_('Total Price')), 4, 0)
    d_grid.addWidget(self.details_total_price_l, 4, 1, 1, 4)

    # layout
    vbox_g = QVBoxLayout()
    vbox_g.addLayout(d_grid)
    vbox_g.addStretch()

    col_1 = QWidget()
    col_1.setLayout(grid)

    col_2 = QWidget()
    col_2.setLayout(vbox_g)

    hbox = QVBoxLayout(self)
    hbox.addWidget(col_1)
    hbox.addWidget(col_2)
    hbox.addWidget(self.rec_buttons_widget)
    self.update_form()

  def update_form(self):
    loop = asyncio.get_event_loop()
    coro = SwapTransaction.parse_from_hex(self.signed_partial_e.toPlainText(), self.wallet)
    future = asyncio.run_coroutine_threadsafe(coro, loop)
    result = None
    error = None
    try:
      result = future.result(timeout=5.0)
      if not result:
        error = "Timed out validating partial transaction"
    except BufferError as ex:
      error = ex

    self.execute_swap_button.setEnabled(result is not None)
    if result:
      self.details_valid_l.setText(_("Yes"))

      if result.trade_type == "buy":
        self.details_order_type_l.setText(_("Buy Order (You are selling)"))
      elif result.trade_type == "sell":
        self.details_order_type_l.setText(_("Sell Order (You are buying)"))
      elif result.trade_type == "trade":
        self.details_order_type_l.setText(_("Trade Order (You are exchange assets for other assets)"))

      self.details_asset_l.setText("{}x [{}]".format(result.quantity, result.asset))
      self.details_unit_price_l.setText("{}x [{}] per [{}]"\
          .format(result.unit_price, result.currency.upper(), result.asset.upper()))
      self.details_total_price_l.setText("{}x [{}]"\
          .format(result.total_price, result.currency.upper()))

      #Add assets to local cache
      def test_asset(asset):
        if asset != "rvn" and asset not in self.wallet.get_assets():
          print("Adding {} to asset cache".format(asset))
          self.wallet.add_asset(asset)
      test_asset(result.in_type)
      test_asset(result.out_type)

      self.parsed_swap = result
    else:
      self.details_valid_l.setText(_("No - {}").format(error) if error else _("No"))
      self.details_order_type_l.clear()
      self.details_asset_l.clear()
      self.details_unit_price_l.clear()
      self.details_total_price_l.clear()

    

  def update_receive_qr(self, *args):
    print("Soemthing!")
  
  def get_decimal_point(self):
    return self.config.get_decimal_point()
    
  def update_receive_address_styling(self):
    addr = str(self.receive_address_e.text())
    if is_address(addr) and self.wallet.is_used(addr):
      self.receive_address_e.setStyleSheet(ColorScheme.RED.as_stylesheet(True))
      self.receive_address_e.setToolTip(_("This address has already been used. "
                                          "For better privacy, do not reuse it for new payments."))
    else:
      self.receive_address_e.setStyleSheet("")
      self.receive_address_e.setToolTip("")
  
  def clear_swap(self, _):
    print("Clear")

  def execute_swap(self, _):
    if self.parsed_swap:
      print("Execute!")
      self.execute_swap_action.emit(self.parsed_swap)
