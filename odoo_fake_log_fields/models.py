from odoo import SUPERUSER_ID, api
from collections import defaultdict
from odoo import models
from odoo.exceptions import AccessError
from odoo.tools.misc import clean_context
from operator import attrgetter
from odoo.tools import groupby
from odoo.tools.translate import _
from psycopg2.extensions import AsIs
import hashlib

import logging
_logger = logging.getLogger(__name__)


LOG_ACCESS_COLUMNS = ['create_uid', 'create_date', 'write_uid', 'write_date']

HASH_REQ_COLUMNS = {'create_uid', 'create_date',
                    'write_uid', 'write_date', 'hashed_value'}


def calc_hash(self, hash_key, vals):

    string_to_hash = u"%s%s%s%s%s" % (hash_key,
                                      vals['create_uid'],
                                      vals['create_date'],
                                      vals['write_uid'],
                                      vals['write_date'])
    return hashlib.new("sha1", string_to_hash.encode('utf-8')).hexdigest()


def check_multiple_audit_hash(self, vals_list):
    hash_key = 'lolo'
    for vals in vals_list:
        if vals.keys() >= HASH_REQ_COLUMNS and self.calc_hash(hash_key, vals) == vals['hashed_value']:
            continue
        else:
            return False
    return True


def check_audit_hash(self, vals):
    hash_key = 'lolo'
    return vals.keys() >= HASH_REQ_COLUMNS and self.calc_hash(hash_key, vals) == vals['hashed_value']


def write(self, vals):
    """ write(vals)

    Updates all records in the current set with the provided values.
s
    :param dict vals: fields to update and the value to set on them e.g::

            {'foo': 1, 'bar': "Qux"}

        will set the field ``foo`` to ``1`` and the field ``bar`` to
        ``"Qux"`` if those are valid (otherwise it will trigger an error).

    :raise AccessError: * if user has no write rights on the requested object
                        * if user tries to bypass access rules for write on the requested object
    :raise ValidationError: if user tries to enter invalid value for a field that is not in selection
    :raise UserError: if a loop would be created in a hierarchy of objects a result of the operation (such as setting an object as its own parent)

    * For numeric fields (:class:`~odoo.fields.Integer`,
      :class:`~odoo.fields.Float`) the value should be of the
      corresponding type
    * For :class:`~odoo.fields.Boolean`, the value should be a
      :class:`python:bool`
    * For :class:`~odoo.fields.Selection`, the value should match the
      selection values (generally :class:`python:str`, sometimes
      :class:`python:int`)
    * For :class:`~odoo.fields.Many2one`, the value should be the
      database identifier of the record to set
    * Other non-relational fields use a string for value

      .. danger::

          for historical and compatibility reasons,
          :class:`~odoo.fields.Date` and
          :class:`~odoo.fields.Datetime` fields use strings as values
          (written and read) rather than :class:`~python:datetime.date` or
          :class:`~python:datetime.datetime`. These date strings are
          UTC-only and formatted according to
          :const:`odoo.tools.misc.DEFAULT_SERVER_DATE_FORMAT` and
          :const:`odoo.tools.misc.DEFAULT_SERVER_DATETIME_FORMAT`
    * .. _openerp/models/relationals/format:

      :class:`~odoo.fields.One2many` and
      :class:`~odoo.fields.Many2many` use a special "commands" format to
      manipulate the set of records stored in/associated with the field.

      This format is a list of triplets executed sequentially, where each
      triplet is a command to execute on the set of records. Not all
      commands apply in all situations. Possible commands are:

      ``(0, 0, values)``
          adds a new record created from the provided ``value`` dict.
      ``(1, id, values)``
          updates an existing record of id ``id`` with the values in
          ``values``. Can not be used in :meth:`~.create`.
      ``(2, id, 0)``
          removes the record of id ``id`` from the set, then deletes it
          (from the database). Can not be used in :meth:`~.create`.
      ``(3, id, 0)``
          removes the record of id ``id`` from the set, but does not
          delete it. Can not be used in
          :meth:`~.create`.
      ``(4, id, 0)``
          adds an existing record of id ``id`` to the set.
      ``(5, 0, 0)``
          removes all records from the set, equivalent to using the
          command ``3`` on every record explicitly. Can not be used in
          :meth:`~.create`.
      ``(6, 0, ids)``
          replaces all existing records in the set by the ``ids`` list,
          equivalent to using the command ``5`` followed by a command
          ``4`` for each ``id`` in ``ids``.
    """
    if not self:
        return True

    self.check_access_rights('write')
    self.check_field_access_rights('write', vals.keys())
    self.check_access_rule('write')
    env = self.env
    audit_hash = self.check_audit_hash(vals)
    if 'hashed_value' in vals:
        del vals['hashed_value']
    bad_names = {'id', 'parent_path'}
    if self._log_access:
        # the superuser can set log_access fields while loading registry
        if not(self.env.uid == SUPERUSER_ID and not self.pool.ready) and not audit_hash:
            bad_names.update(LOG_ACCESS_COLUMNS)

    determine_inverses = defaultdict(list)      # {inverse: fields}
    records_to_inverse = {}                     # {field: records}
    relational_names = []
    protected = set()
    check_company = False
    for fname in vals:

        field = self._fields.get(fname)
        if not field:
            raise ValueError("Invalid field %r on model %r" %
                             (fname, self._name))
        if field.inverse:
            if field.type in ('one2many', 'many2many'):
                # The written value is a list of commands that must applied
                # on the field's current value. Because the field is
                # protected while being written, the field's current value
                # will not be computed and default to an empty recordset. So
                # make sure the field's value is in cache before writing, in
                # order to avoid an inconsistent update.
                self[fname]
            determine_inverses[field.inverse].append(field)
            # DLE P150: `test_cancel_propagation`, `test_manufacturing_3_steps`, `test_manufacturing_flow`
            # TODO: check whether still necessary
            records_to_inverse[field] = self.filtered('id')
        if field.relational or self._field_inverses[field]:
            relational_names.append(fname)
        if field.inverse or (field.compute and not field.readonly):
            if field.store or field.type not in ('one2many', 'many2many'):
                # Protect the field from being recomputed while being
                # inversed. In the case of non-stored x2many fields, the
                # field's value may contain unexpeced new records (created
                # by command 0). Those new records are necessary for
                # inversing the field, but should no longer appear if the
                # field is recomputed afterwards. Not protecting the field
                # will automatically invalidate the field from the cache,
                # forcing its value to be recomputed once dependencies are
                # up-to-date.
                protected.update(self._field_computed.get(field, [field]))
        if fname == 'company_id' or (field.relational and field.check_company):
            check_company = True

    # protect fields being written against recomputation
    with env.protecting(protected, self):
        # determine records depending on values
        self.modified(relational_names)

        real_recs = self.filtered('id')

        # If there are only fields that do not trigger _write (e.g. only
        # determine inverse), the below ensures that `write_date` and
        # `write_uid` are updated (`test_orm.py`, `test_write_date`)
        if self._log_access and self.ids and not audit_hash:

            towrite = env.all.towrite[self._name]
            for record in real_recs:
                towrite[record.id]['write_uid'] = self.env.uid
                towrite[record.id]['write_date'] = False
            self.env.cache.invalidate([
                (self._fields['write_date'], self.ids),
                (self._fields['write_uid'], self.ids),
            ])

        # for monetary field, their related currency field must be cached
        # before the amount so it can be rounded correctly
        for fname in sorted(vals, key=lambda x: self._fields[x].type == 'monetary'):
            if fname in bad_names:
                continue
            field = self._fields[fname]
            field.write(self, vals[fname])

        # determine records depending on new values
        #
        # Call modified after write, because the modified can trigger a
        # search which can trigger a flush which can trigger a recompute
        # which remove the field from the recompute list while all the
        # values required for the computation could not be yet in cache.
        # e.g. Write on `name` of `res.partner` trigger the recompute of
        # `display_name`, which triggers a search on child_ids to find the
        # childs to which the display_name must be recomputed, which
        # triggers the flush of `display_name` because the _order of
        # res.partner includes display_name. The computation of display_name
        # is then done too soon because the parent_id was not yet written.
        # (`test_01_website_reset_password_tour`)
        self.modified(vals)

        if self._parent_store and self._parent_name in vals:
            self.flush([self._parent_name])

        # validate non-inversed fields first
        inverse_fields = [f.name for fs in determine_inverses.values()
                          for f in fs]
        real_recs._validate_fields(set(vals) - set(inverse_fields))

        for fields in determine_inverses.values():
            # inverse records that are not being computed
            try:
                fields[0].determine_inverse(real_recs)
            except AccessError as e:
                if fields[0].inherited:
                    description = self.env[
                        'ir.model']._get(self._name).name
                    raise AccessError(
                        _("%(previous_message)s\n\nImplicitly accessed through '%(document_kind)s' (%(document_model)s).") % {
                            'previous_message': e.args[0],
                            'document_kind': description,
                            'document_model': self._name,
                        }
                    )
                raise

        # validate inversed fields
        real_recs._validate_fields(inverse_fields)

    if check_company and self._check_company_auto:
        self._check_company()
    return True


@api.model_create_multi
@api.returns('self', lambda value: value.id)
def create(self, vals_list):
    """ create(vals_list) -> records

    Creates new records for the model.

    The new records are initialized using the values from the list of dicts
    ``vals_list``, and if necessary those from :meth:`~.default_get`.

    :param list vals_list:
        values for the model's fields, as a list of dictionaries::

            [{'field_name': field_value, ...}, ...]

        For backward compatibility, ``vals_list`` may be a dictionary.
        It is treated as a singleton list ``[vals]``, and a single record
        is returned.

        see :meth:`~.write` for details

    :return: the created records
    :raise AccessError: * if user has no create rights on the requested object
                        * if user tries to bypass access rules for create on the requested object
    :raise ValidationError: if user tries to enter invalid value for a field that is not in selection
    :raise UserError: if a loop would be created in a hierarchy of objects a result of the operation (such as setting an object as its own parent)
    """
    if not vals_list:
        return self.browse()

    self = self.browse()
    self.check_access_rights('create')
    audit_hash = self.check_multiple_audit_hash(vals_list)

    bad_names = {'id', 'parent_path'}
    if self._log_access:
        # the superuser can set log_access fields while loading registry
        if not(self.env.uid == SUPERUSER_ID and not self.pool.ready) and not audit_hash:
            bad_names.update(LOG_ACCESS_COLUMNS)

    # classify fields for each record
    data_list = []
    inversed_fields = set()

    for vals in vals_list:
        # add missing defaults
        vals = self._add_missing_default_values(vals)
        #audit_hash = self.check_audit_hash(vals)
        if 'hashed_value' in vals:
            del vals['hashed_value']
        # distribute fields into sets for various purposes
        data = {}
        data['stored'] = stored = {}
        data['inversed'] = inversed = {}
        data['inherited'] = inherited = defaultdict(dict)
        data['protected'] = protected = set()
        data['audit_hash'] = audit_hash

        for key, val in vals.items():
            if key in bad_names:
                continue
            field = self._fields.get(key)
            if not field:
                raise ValueError(
                    "Invalid field %r on model %r" % (key, self._name))
            if field.company_dependent:
                irprop_def = self.env['ir.property'].get(key, self._name)
                cached_def = field.convert_to_cache(irprop_def, self)
                cached_val = field.convert_to_cache(val, self)
                if cached_val == cached_def:
                    # val is the same as the default value defined in
                    # 'ir.property'; by design, 'ir.property' will not
                    # create entries specific to these records; skipping the
                    # field inverse saves 4 SQL queries
                    continue
            if field.store:
                stored[key] = val
            if field.inherited:
                inherited[field.related_field.model_name][key] = val
            elif field.inverse:
                inversed[key] = val
                inversed_fields.add(field)
            # protect non-readonly computed fields against (re)computation
            if field.compute and not field.readonly:
                protected.update(self._field_computed.get(field, [field]))

        data_list.append(data)

    # create or update parent records
    for model_name, parent_name in self._inherits.items():
        parent_data_list = []
        for data in data_list:
            if not data['stored'].get(parent_name):
                parent_data_list.append(data)
            elif data['inherited'][model_name]:
                parent = self.env[model_name].browse(
                    data['stored'][parent_name])
                parent.write(data['inherited'][model_name])

        if parent_data_list:
            parents = self.env[model_name].create([
                data['inherited'][model_name]
                for data in parent_data_list
            ])
            for parent, data in zip(parents, parent_data_list):
                data['stored'][parent_name] = parent.id

    # create records with stored fields
    records = self._create(data_list)

    # protect fields being written against recomputation
    protected = [(data['protected'], data['record']) for data in data_list]
    with self.env.protecting(protected):
        # group fields by inverse method (to call it once), and order groups
        # by dependence (in case they depend on each other)
        field_groups = (fields for _inv, fields in groupby(
            inversed_fields, attrgetter('inverse')))
        for fields in field_groups:
            # determine which records to inverse for those fields
            inv_names = {field.name for field in fields}
            rec_vals = [
                (data['record'], {
                    name: data['inversed'][name]
                    for name in inv_names
                    if name in data['inversed']
                })
                for data in data_list
                if not inv_names.isdisjoint(data['inversed'])
            ]

            # If a field is not stored, its inverse method will probably
            # write on its dependencies, which will invalidate the field on
            # all records. We therefore inverse the field record by record.
            if all(field.store or field.company_dependent for field in fields):
                batches = [rec_vals]
            else:
                batches = [[rec_data] for rec_data in rec_vals]

            for batch in batches:
                for record, vals in batch:
                    record._update_cache(vals)
                batch_recs = self.concat(
                    *(record for record, vals in batch))
                fields[0].determine_inverse(batch_recs)

    # check Python constraints for non-stored inversed fields
    for data in data_list:
        data['record']._validate_fields(
            set(data['inversed']) - set(data['stored']))

    if self._check_company_auto:
        records._check_company()
    return records


@api.model
def _create(self, data_list):
    """ Create records from the stored field values in ``data_list``. """
    assert data_list
    cr = self.env.cr
    quote = '"{}"'.format

    # insert rows
    ids = []                        # ids of created records
    other_fields = set()            # non-column fields
    translated_fields = set()       # translated fields

    # column names, formats and values (for common fields)
    columns0 = [('id', "nextval(%s)", self._sequence)]
    if self._log_access and not data_list[0]['audit_hash']:
        columns0.append(('create_uid', "%s", self._uid))
        columns0.append(
            ('create_date', "%s", AsIs("(now() at time zone 'UTC')")))
        columns0.append(('write_uid', "%s", self._uid))
        columns0.append(
            ('write_date', "%s", AsIs("(now() at time zone 'UTC')")))

    for data in data_list:
        # determine column values
        stored = data['stored']
        columns = [column for column in columns0 if column[0] not in stored]
        for name, val in sorted(stored.items()):
            field = self._fields[name]
            assert field.store

            if field.column_type:
                col_val = field.convert_to_column(val, self, stored)
                columns.append((name, field.column_format, col_val))
                if field.translate is True:
                    translated_fields.add(field)
            else:
                other_fields.add(field)

        # insert a row with the given columns
        query = "INSERT INTO {} ({}) VALUES ({}) RETURNING id".format(
            quote(self._table),
            ", ".join(quote(name) for name, fmt, val in columns),
            ", ".join(fmt for name, fmt, val in columns),
        )
        params = [val for name, fmt, val in columns]
        cr.execute(query, params)
        ids.append(cr.fetchone()[0])

    # put the new records in cache, and update inverse fields, for many2one
    #
    # cachetoclear is an optimization to avoid modified()'s cost until
    # other_fields are processed
    cachetoclear = []
    records = self.browse(ids)
    inverses_update = defaultdict(list)     # {(field, value): ids}
    for data, record in zip(data_list, records):
        data['record'] = record
        # DLE P104: test_inherit.py, test_50_search_one2many
        vals = dict({k: v for d in data['inherited'].values()
                     for k, v in d.items()}, **data['stored'])
        set_vals = list(vals) + LOG_ACCESS_COLUMNS + \
            [self.CONCURRENCY_CHECK_FIELD, 'id', 'parent_path']
        for field in self._fields.values():
            if field.type in ('one2many', 'many2many'):
                self.env.cache.set(record, field, ())
            elif field.related and not field.column_type:
                self.env.cache.set(
                    record, field, field.convert_to_cache(None, record))
            # DLE P123: `test_adv_activity`, `test_message_assignation_inbox`, `test_message_log`, `test_create_mail_simple`, ...
            # Set `mail.message.parent_id` to False in cache so it doesn't do the useless SELECT when computing the modified of `child_ids`
            # in other words, if `parent_id` is not set, no other message `child_ids` are impacted.
            # + avoid the fetch of fields which are False. e.g. if a boolean field is not passed in vals and as no default set in the field attributes,
            # then we know it can be set to False in the cache in the case
            # of a create.
            elif field.name not in set_vals and not field.compute:
                self.env.cache.set(
                    record, field, field.convert_to_cache(None, record))
        for fname, value in vals.items():
            field = self._fields[fname]
            if field.type in ('one2many', 'many2many'):
                cachetoclear.append((record, field))
            else:
                cache_value = field.convert_to_cache(value, record)
                self.env.cache.set(record, field, cache_value)
                if field.type in ('many2one', 'many2one_reference') and record._field_inverses[field]:
                    inverses_update[(field, cache_value)].append(record.id)

    for (field, value), record_ids in inverses_update.items():
        field._update_inverses(self.browse(record_ids), value)

    # update parent_path
    records._parent_store_create()

    # protect fields being written against recomputation
    protected = [(data['protected'], data['record']) for data in data_list]
    with self.env.protecting(protected):
        # mark computed fields as todo
        records.modified(self._fields, create=True)

        if other_fields:
            # discard default values from context for other fields
            others = records.with_context(clean_context(self._context))
            for field in sorted(other_fields, key=attrgetter('_sequence')):
                field.create([
                    (other, data['stored'][field.name])
                    for other, data in zip(others, data_list)
                    if field.name in data['stored']
                ])

            # mark fields to recompute
            records.modified(
                [field.name for field in other_fields], create=True)

        # if value in cache has not been updated by other_fields, remove it
        for record, field in cachetoclear:
            if self.env.cache.contains(record, field) and not self.env.cache.get(record, field):
                self.env.cache.remove(record, field)

    # check Python constraints for stored fields
    records._validate_fields(
        name for data in data_list for name in data['stored'])
    records.check_access_rule('create')

    # add translations
    if self.env.lang and self.env.lang != 'en_US':
        Translations = self.env['ir.translation']
        for field in translated_fields:
            tname = "%s,%s" % (field.model_name, field.name)
            for data in data_list:
                if field.name in data['stored']:
                    record = data['record']
                    val = data['stored'][field.name]
                    Translations._set_ids(
                        tname, 'model', self.env.lang, record.ids, val, val)

    return records


models.BaseModel.calc_hash = calc_hash
models.BaseModel.check_multiple_audit_hash = check_multiple_audit_hash
models.BaseModel.check_audit_hash = check_audit_hash
models.BaseModel.write = write
models.BaseModel.create = create
models.BaseModel._create = _create
