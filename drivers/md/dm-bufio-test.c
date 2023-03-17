#include <linux/device-mapper.h>
#include <linux/dm-bufio.h>
#include <linux/kthread.h>
#include <linux/module.h>

#define DM_MSG_PREFIX "bufio-test"

/*-----------------------------------------*/

enum instruction {
	I_HALT,

	I_LIT,
	I_SUB,
	I_ADD,

	I_NEW_BUF,
	I_READ_BUF,
	I_GET_BUF,
	I_PUT_BUF,
	I_MARK_DIRTY,
	I_WRITE_ASYNC,
	I_WRITE_SYNC,
	I_FLUSH,
	I_FORGET,
	I_FORGET_RANGE,

	I_LOOP,
	I_STAMP,
	I_VERIFY,

	I_CHECKPOINT,
};

#define NR_REGISTERS 32

struct vm {
	struct dm_bufio_client *bufio;
	uint64_t registers[NR_REGISTERS];

	uint8_t *code_begin;
	uint8_t *code_end;
	uint8_t *pc;
};

static void init_vm(struct vm *vm, struct dm_bufio_client *bufio,
		    void *code, unsigned len)
{
	unsigned i;

	vm->bufio = bufio;

	for (i = 0; i < NR_REGISTERS; i++)
		vm->registers[i] = 0;

	vm->code_begin = (uint8_t *) code;
	vm->code_end = vm->code_begin + len;
	vm->pc = vm->code_begin;
}

static int has_space(struct vm *vm, size_t len)
{
	if (vm->pc > vm->code_end)
		return false;

	return (vm->code_end - vm->pc) >= len;
}

static uint8_t read_u8(struct vm *vm, uint8_t *u8)
{
	if (!has_space(vm, sizeof(*u8)))
		return -ENOMEM;

	*u8 = *vm->pc;
	vm->pc += 1;
	return 0;
}

static uint16_t read_u16(struct vm *vm, uint16_t *u16)
{
	if (!has_space(vm, sizeof(*u16)))
		return -ENOMEM;

	memcpy(u16, vm->pc, 2);
	vm->pc += 2;
	return 0;
}

static uint32_t read_u32(struct vm *vm, uint32_t *u32)
{
	if (!has_space(vm, sizeof(*u32)))
		return -ENOMEM;

	memcpy(u32, vm->pc, 4);
	vm->pc += 4;
	return 0;
}

static int exec_instr(struct vm *vm, bool *halted)
{
	int r;
	void *ptr;
	uint8_t u8, reg1, reg2;
	uint16_t u16;
	uint32_t u32, u32_2;
	struct dm_buffer *b;
	enum instruction instr;

	*halted = false;

	r = read_u8(vm, &u8);
	if (r)
		return r;

	instr = (enum instruction) u8;
	switch (instr) {
	case I_HALT:
		*halted = true;
		break;

	case I_LIT:
		r = read_u32(vm, &u32);
		if (r)
			return r;

		r = read_u8(vm, &u8);
		if (r)
			return r;

		vm->registers[u8] = u32;
		break;

	case I_SUB:
		r = read_u8(vm, &reg1);
		if (r)
			return r;

		r = read_u8(vm, &u8);
		if (r)
			return r;

		vm->registers[reg1] -= u8;
		break;

	case I_ADD:
		r = read_u8(vm, &reg1);
		if (r)
			return r;

		r = read_u8(vm, &u8);
		if (r)
			return r;

		vm->registers[reg1] += u8;
		break;

	case I_NEW_BUF:
		// block
		r = read_u8(vm, &reg1);
		if (r)
			return r;

		// dest
		r = read_u8(vm, &reg2);
		if (r)
			return r;

		ptr = dm_bufio_new(vm->bufio, vm->registers[reg1], &b);
		if (!ptr || IS_ERR(ptr)) {
			pr_alert("bufio_new(%llu) failed", (unsigned long long) vm->registers[reg1]);
			BUG_ON(1);
		}

		BUG_ON(!b);
		vm->registers[reg2] = (uint64_t) b;
		break;

	case I_READ_BUF:
		// block
		r = read_u8(vm, &reg1);
		if (r)
			return r;

		// dest
		r = read_u8(vm, &reg2);
		if (r)
			return r;

		ptr = dm_bufio_read(vm->bufio, (sector_t) vm->registers[reg1], &b);
		if (!ptr || IS_ERR(ptr)) {
			pr_alert("bufio_read(%llu) failed", (unsigned long long) vm->registers[reg1]);
			BUG();
		}

		BUG_ON(!b);
		vm->registers[reg2] = (uint64_t) b;
		break;

	case I_GET_BUF:
		// block
		r = read_u8(vm, &reg1);
		if (r)
			return r;

		// register
		r = read_u8(vm, &reg2);
		if (r)
			return r;

		ptr = dm_bufio_get(vm->bufio, (sector_t) vm->registers[reg1], &b);
		if (IS_ERR(ptr)) {
			pr_alert("bufio_read(%llu) failed", (unsigned long long) vm->registers[reg1]);
			BUG();
		}

		if (ptr) {
			BUG_ON(!b);
			vm->registers[reg2] = (uint64_t) b;
		}
 		break;

	case I_PUT_BUF:
		// register
		r = read_u8(vm, &reg1);
		if (r)
			return r;

		BUG_ON(!vm->registers[reg1]);
		dm_bufio_release((struct dm_buffer *) vm->registers[reg1]);
		break;

	case I_MARK_DIRTY:
		// register
		r = read_u8(vm, &reg1);
		if (r)
			return r;

		BUG_ON(!vm->registers[reg1]);
		dm_bufio_mark_buffer_dirty((struct dm_buffer *) vm->registers[reg1]);
		break;

	case I_WRITE_ASYNC:
		dm_bufio_write_dirty_buffers_async(vm->bufio);
		break;

	case I_WRITE_SYNC:
		r = dm_bufio_write_dirty_buffers(vm->bufio);
		if (r) {
			pr_alert("write_sync failed %d", r);
			return r;
		}
		break;

	case I_FLUSH:
		r = dm_bufio_issue_flush(vm->bufio);
		if (r)
			return r;
		break;

	case I_FORGET:
		// block
		r = read_u32(vm, &u32);
		if (r)
			return r;

		dm_bufio_forget(vm->bufio, (sector_t) u32);
		break;

	case I_FORGET_RANGE:
		// block
		r = read_u32(vm, &u32);
		if (r)
			return r;

		// len
		r = read_u32(vm, &u32_2);
		if (r)
			return r;
		dm_bufio_forget_buffers(vm->bufio, (sector_t) u32, (sector_t) u32_2);
		break;

	case I_LOOP:
		// addr
		r = read_u16(vm, &u16);
		if (r)
			return r;

		// count
		r = read_u8(vm, &reg1);
		if (r)
			return r;

		if (vm->registers[reg1]) {
			vm->pc = vm->code_begin + u16;
			vm->registers[reg1]--;
		}
		break;

	case I_STAMP:
		r = read_u8(vm, &reg1);  // register containing buf
		if (r)
			return r;

		r = read_u8(vm, &reg2);  // contains value to stamp
		if (r)
			return r;

		b = (struct dm_buffer *) vm->registers[reg1];
		{
			unsigned i;
			uint32_t *data = dm_bufio_get_block_data(b);
			for (i = 0; i < 1024; i++)
				data[i] = (uint32_t) vm->registers[reg2];
		}
		break;

	case I_VERIFY:
		r = read_u8(vm, &reg1);  // register containing buf
		if (r)
			return r;

		r = read_u8(vm, &reg2);  // contains value to stamp
		if (r)
			return r;

		b = (struct dm_buffer *) vm->registers[reg1];
		{
			unsigned i;
			uint32_t *data = dm_bufio_get_block_data(b);
			for (i = 0; i < 1024; i++)
				BUG_ON(data[i] != (uint32_t) vm->registers[reg2]);
		}
		break;

	case I_CHECKPOINT:
		r = read_u8(vm, &u8);
		if (r)
			return r;

		pr_alert("checkpoint %u", (unsigned) u8);
		break;

	default:
		pr_alert("unknown instruction");
		return -EINVAL;
	}

	return 0;
}

static int exec(struct vm *vm)
{
	int r;
	bool halted = false;

	while (!halted) {
		r = exec_instr(vm, &halted);
		if (r)
			return r;
	}

	return 0;
}

/*-----------------------------------------*/

struct bufio_test_c {
	struct dm_bufio_client *bufio;
	struct dm_dev *dev;

	unsigned block_size;
	sector_t block_mask;
};

static void dtr(struct dm_target *ti)
{
	struct bufio_test_c *t = ti->private;

	if (t->bufio && !IS_ERR(t->bufio))
		dm_bufio_client_destroy(t->bufio);
	if (t->dev)
		dm_put_device(ti, t->dev);

	kfree(t);
}

static int ctr(struct dm_target *ti, unsigned int argc, char **argv)
{
	struct bufio_test_c *t;
	int r;

	if (argc != 1) {
		ti->error = "Requires 1 argument";
		return -EINVAL;
	}

	t = kzalloc(sizeof(*t), GFP_KERNEL);
	if (!t) {
		ti->error = "Cannot allocate context";
		return -ENOMEM;
	}
	t->block_size = 4096;
	t->block_mask = t->block_size - 1;

	r = dm_get_device(ti, argv[0], dm_table_get_mode(ti->table), &t->dev);
	if (r) {
		ti->error = "Device lookup failed";
		return -EINVAL;
	}

	t->bufio = dm_bufio_client_create(t->dev->bdev, t->block_size,
					   1, 0, NULL, NULL, 0);
	if (IS_ERR(t->bufio)) {
		ti->error = "Couldn't create bufio client";
		dm_put_device(ti, t->dev);
		r = PTR_ERR(t->bufio);
		return -EINVAL;
	}
	ti->num_flush_bios = 1;
	ti->num_discard_bios = 1;
	ti->num_secure_erase_bios = 1;
	ti->num_write_zeroes_bios = 1;
	ti->private = t;

	return 0;
}

static int program_thread(void *context)
{
	struct bio *bio = context;
	struct bufio_test_c *t = (struct bufio_test_c *) bio->bi_next;

	int r, seg = 0;
	void *data;
	unsigned len;
	struct vm vm;
	struct bio_vec bvec;

	bio_for_each_segment(bvec, bio, bio->bi_iter) {
		data = kmap_local_page(bvec.bv_page);
		len = bvec.bv_len;
		init_vm(&vm, t->bufio, data, len);

		pr_alert("calling exec on program len %u, seg = %d, bio = %p", len, seg++, bio);
		r = exec(&vm);
		pr_alert("complete bio = %p", bio);

		if (r)
			bio_io_error(bio);
		else
			bio_endio(bio);
	}

	return 0;
}

static int map(struct dm_target *ti, struct bio *bio)
{
	struct task_struct *tid;
	struct bufio_test_c *t = ti->private;

	if (bio_op(bio) == REQ_OP_WRITE) {
		bio->bi_next = (struct bio *) t;   // FIXME: hack
		tid = kthread_create(program_thread, bio, "bufio-test");
		if (IS_ERR(tid)) {
			pr_alert("Failed to create thread for bufio test program");
			bio_io_error(bio);
		}
		wake_up_process(tid);

		return DM_MAPIO_SUBMITTED;
	} else {
		// Everything else gets passed through.
		bio_set_dev(bio, t->dev->bdev);
		return DM_MAPIO_REMAPPED;
	}
}

static void postsuspend(struct dm_target *ti)
{
}

static void status(struct dm_target *ti, status_type_t type,
		   unsigned int status_flags, char *result, unsigned int maxlen)
{
	struct bufio_test_c *t = ti->private;
	int sz = 0;

	switch (type) {
	case STATUSTYPE_TABLE:
		DMEMIT("%s", t->dev->name);
		break;
	case STATUSTYPE_INFO:
		// FIXME: emit some stats
		break;
	case STATUSTYPE_IMA:
		*result = '\0';
	}
}

static int prepare_ioctl(struct dm_target *ti, struct block_device **bdev)
{
	struct bufio_test_c *t = ti->private;
	struct dm_dev *dev = t->dev;

	*bdev = dev->bdev;

	return 0;
}

static int iterate_devices(struct dm_target *ti,
			   iterate_devices_callout_fn fn, void *data)
{
	struct bufio_test_c *t = ti->private;
	return fn(ti, t->dev, 0, ti->len, data);
}

static int message(struct dm_target *ti, unsigned int argc, char **argv,
		   char *result, unsigned int maxlen)
{
	return 0;
}

static struct target_type bufio_test_target = {
	.name		 = "bufio_test",
	.version	 = {1, 0, 0},
	.module		 = THIS_MODULE,
	.ctr		 = ctr,
	.dtr		 = dtr,
	.map		 = map,
	.status		 = status,
	.postsuspend	 = postsuspend,
	.iterate_devices = iterate_devices,
	.prepare_ioctl	 = prepare_ioctl,
	.message	 = message,
};

static int __init dm_bufio_test_init(void)
{
	return dm_register_target(&bufio_test_target);
}

static void __exit dm_bufio_test_exit(void)
{
	dm_unregister_target(&bufio_test_target);
}

/* Module hooks */
module_init(dm_bufio_test_init);
module_exit(dm_bufio_test_exit);

MODULE_DESCRIPTION(DM_NAME " bufio test target");
MODULE_AUTHOR("Joe Thornber <dm-devel@redhat.com>");
MODULE_LICENSE("GPL");