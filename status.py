# -*- coding: utf-8 -*-
from __future__ import division, print_function, unicode_literals
from collections import OrderedDict
import logging

from logging_helpers import _L
from markdown2pango import markdown2pango
from pygtkhelpers.gthreads import gtk_threadsafe
import gtk
import path_helpers as ph
import pygtkhelpers as pgh
import si_prefix as si


PLUGIN_PATH = ph.path(__file__).parent.realpath()
CHIP_INSERTED_IMAGE_PATH = PLUGIN_PATH.joinpath('dropbot-chip-inserted.png')
CHIP_REMOVED_IMAGE_PATH = PLUGIN_PATH.joinpath('dropbot.png')


class DropBotStatusView(pgh.delegates.SlaveView):
    def create_ui(self):
        hbox = gtk.HBox()

        image = gtk.Image()
        image.props.xpad = 10
        image.props.ypad = 0
        event_box = gtk.EventBox()
        event_box.add(image)
        hbox.pack_start(event_box, fill=False, expand=False)

        properties = OrderedDict([('Voltage', 'Root mean square **actuation '
                                   'voltage**.'),
                                  ('Capacitance', '**Load capacitance** of '
                                   'actuated channels.'),
                                  ('c<sub>device</sub>',
                                   '**Capacitance per unit area** for '
                                   'electrodes covered by liquid.'),
                                  ('Force', '**Force applied** to liquid on '
                                   'actuated electrodes.')])
        table = gtk.Table(rows=len(properties), columns=2)
        for i, (name_i, description_i) in enumerate(properties.items()):
            name_label_i = gtk.Label(markdown2pango('**%s:**' %
                                                    name_i).strip())
            value_label_i = gtk.Label()
            description_pango_i = markdown2pango(description_i).strip()
            name_label_i.set_tooltip_markup(description_pango_i)
            value_label_i.set_tooltip_markup(description_pango_i)
            name_label_i.props.use_markup = True
            name_label_i.props.xalign = 1
            value_label_i.props.name = name_i
            value_label_i.props.use_markup = True
            value_label_i.props.xalign = 0
            table.attach(name_label_i, 0, 1, i, i + 1, xpadding=5)
            table.attach(value_label_i, 1, 2, i, i + 1, xpadding=5)

        hbox.pack_start(table, fill=False, expand=False)
        hbox.show_all()

        self.widget.add(hbox)
        self.status_labels = {child_i.name: child_i
                              for child_i in table.get_children()
                              if child_i.name}
        for prop in ('capacitance', 'voltage', 'c_device', 'force'):
            setattr(self, prop, None)
        self.event_box = event_box
        self.image = image
        self.on_disconnected()

    def _set_image(self, image_path):
        image_size = 80

        pixbuf = gtk.gdk.pixbuf_new_from_file(image_path)
        if pixbuf.props.width > pixbuf.props.height:
            scale = image_size / pixbuf.props.width
        else:
            scale = image_size / pixbuf.props.height
        width = int(scale * pixbuf.props.width)
        height = int(scale * pixbuf.props.height)
        pixbuf = pixbuf.scale_simple(width, height, gtk.gdk.INTERP_BILINEAR)
        self.image.set_from_pixbuf(pixbuf)

    @property
    def status(self):
        return self._status

    @status.setter
    def status(self, value):
        self._status = value
        sections = ['## %(title)s ##' % value]
        props_list = ''.join(['\n - **%s:** `%s`' % (k, v)
                              for k, v in value.get('properties', {}).items()])
        if props_list:
            sections.append(props_list)
        if 'footer' in value:
            sections.extend(['', value['footer']])
        text = markdown2pango('\n'.join(sections))
        logger = _L()
        if logger.getEffectiveLevel() <= logging.DEBUG:
            map(logger.debug, text.splitlines())
        gtk_threadsafe(self.event_box.set_tooltip_markup)(text)

    @gtk_threadsafe
    def on_disconnected(self):
        self._set_image(CHIP_REMOVED_IMAGE_PATH)
        self.status = {'title': 'DropBot', 'footer': '**_No connection._**'}
        self.event_box.modify_bg(gtk.STATE_NORMAL,
                                 # Medium red.
                                 gtk.gdk.color_parse('#f15854'))

    @gtk_threadsafe
    def on_connected(self, dropbot):
        properties = dropbot.properties
        self.status = {'title': 'DropBot v%s' % dropbot.hardware_version,
                       'properties': {'Firmware': properties.software_version,
                                      'UUID': dropbot.uuid,
                                      'Number of channels':
                                      dropbot.number_of_channels}}
        self.event_box.modify_bg(gtk.STATE_NORMAL,
                                 # Medium yellow.
                                 gtk.gdk.color_parse('#decf3f'))

    @property
    def chip_inserted(self):
        raise NotImplementedError

    @chip_inserted.setter
    @gtk_threadsafe
    def chip_inserted(self, value):
        image_name = (CHIP_INSERTED_IMAGE_PATH
                      if value else CHIP_REMOVED_IMAGE_PATH)
        medium_yellow = gtk.gdk.color_parse('#decf3f')
        medium_green = gtk.gdk.color_parse('#60bd68')
        color =  medium_green if value else medium_yellow
        self._set_image(ph.path(__file__).parent
                        .joinpath(image_name))
        self.event_box.modify_bg(gtk.STATE_NORMAL, color)
        status = self.status.copy()
        if value:
            status['footer'] = '**_Chip inserted_.**'
        else:
            status['footer'] = '**_No chip inserted_.**'
        self.status = status

    @property
    def capacitance(self):
        raise NotImplementedError

    @capacitance.setter
    @gtk_threadsafe
    def capacitance(self, value):
        text = markdown2pango('`%sF`' % (si.si_format(value)
                                         if value else '- '))
        self.status_labels['Capacitance'].set_markup(text.strip())

    @property
    def voltage(self):
        raise NotImplementedError

    @voltage.setter
    @gtk_threadsafe
    def voltage(self, value):
        text = markdown2pango('`%sV`' % (si.si_format(value)
                                         if value else '- '))
        self.status_labels['Voltage'].set_markup(text.strip())

    @property
    def c_device(self):
        raise NotImplementedError

    @c_device.setter
    @gtk_threadsafe
    def c_device(self, value):
        text = markdown2pango('`%sF/mm`<sup>2</sup>' % (si.si_format(value)
                                                        if value else '- '))
        self.status_labels['c<sub>device</sub>'].set_markup(text.strip())

    @property
    def force(self):
        raise NotImplementedError

    @force.setter
    @gtk_threadsafe
    def force(self, value):
        text = markdown2pango('`%sN/mm`' % (si.si_format(value)
                                            if value else '- '))
        self.status_labels['Force'].set_markup(text.strip())

    def clear(self):
        self.capacitance = None
        self.voltage = None
        self.c_device = None
        self.force = None
