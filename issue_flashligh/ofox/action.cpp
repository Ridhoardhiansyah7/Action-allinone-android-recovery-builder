/*
        Copyright 2013 bigbiff/Dees_Troy TeamWin
        This file is part of TWRP/TeamWin Recovery Project.

        Copyright (C) 2018-2025 OrangeFox Recovery Project
        This file is part of the OrangeFox Recovery Project.

        TWRP is free software: you can redistribute it and/or modify
        it under the terms of the GNU General Public License as published by
        the Free Software Foundation, either version 3 of the License, or
        (at your option) any later version.

        TWRP is distributed in the hope that it will be useful,
        but WITHOUT ANY WARRANTY; without even the implied warranty of
        MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
        GNU General Public License for more details.

        You should have received a copy of the GNU General Public License
        along with TWRP.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/ioctl.h>
#include <linux/input.h>
#include <time.h>
#include <unistd.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <dirent.h>
#include <private/android_filesystem_config.h>
#include <android-base/properties.h>

#include <string>
#include <sstream>
#include "../partitions.hpp"
#include "../twrp-functions.hpp"
#include "../twrpRepacker.hpp"
#include "../openrecoveryscript.hpp"

#include "twinstall/adb_install.h"

#include "fuse_sideload.h"
#include "blanktimer.hpp"
#include "twinstall.h"
#include "../twrpDigest/twrpSHA.hpp"
#include "../twrpDigestDriver.hpp"

#include "../orangefox.hpp"
#include "../twrpinstall/include/twinstall/install.h"

extern "C" {
#include "../twcommon.h"
#include "../variables.h"
#include "cutils/properties.h"
#include "twinstall/adb_install.h"
};
#include "set_metadata.h"
#include "minuitwrp/minui.h"

#include "rapidxml.hpp"
#include "objects.hpp"
#include "tw_atomic.hpp"

GUIAction::mapFunc GUIAction::mf;
std::set < string > GUIAction::setActionsRunningInCallerThread;
static string zip_queue[10];
static int zip_queue_index;
pid_t sideload_child_pid;
extern GUITerminal* term;
extern std::vector<users_struct> Users_List;

static void *ActionThread_work_wrapper(void *data);

class ActionThread
{
public:
  ActionThread();
  ~ActionThread();

  void threadActions(GUIAction * act);
  void run(void *data);
private:
  friend void *ActionThread_work_wrapper(void *);
  struct ThreadData
  {
    ActionThread *this_;
    GUIAction *act;
    ThreadData(ActionThread * this_, GUIAction * act):this_(this_), act(act)
    {
    }
  };

  pthread_t m_thread;
  bool m_thread_running;
  pthread_mutex_t m_act_lock;
};

static ActionThread action_thread;        // for all kinds of longer running actions
static ActionThread cancel_thread;        // for longer running "cancel" actions

static void *ActionThread_work_wrapper(void *data)
{
  static_cast < ActionThread::ThreadData * >(data)->this_->run(data);
  return NULL;
}

ActionThread::ActionThread()
{
  m_thread_running = false;
  DataManager::SetValue("tw_action_thread_running", "0");
  pthread_mutexattr_t attr;
  pthread_mutexattr_init(&attr);
  pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&m_act_lock, &attr);
  pthread_mutexattr_destroy(&attr);
}

ActionThread::~ActionThread()
{
  pthread_mutex_lock(&m_act_lock);
  if (m_thread_running)
    {
      pthread_mutex_unlock(&m_act_lock);
      pthread_join(m_thread, NULL);
    }
  else
    {
      pthread_mutex_unlock(&m_act_lock);
    }
  pthread_mutex_destroy(&m_act_lock);
}

// custom encryption kludge - DJ9
static bool Hide_Reboot_Kludge_Fix(string FuncName)
{
  return (FuncName == "need_reboot");
}
// kludge - DJ9

void ActionThread::threadActions(GUIAction * act)
{
  pthread_mutex_lock(&m_act_lock);
  if (m_thread_running)
    {
      pthread_mutex_unlock(&m_act_lock);
       if (! Hide_Reboot_Kludge_Fix(act->mActions[0].mFunction))
       {
          if (act->mActions[0].mFunction == "adb")
                    LOGINFO
                    ("Another threaded action is already running -- not running %lu actions starting with '%s'\n", (unsigned long)act->mActions.size(), act->mActions[0].mFunction.c_str());
          else
                    LOGERR
              ("Another threaded action is already running -- not running %lu actions starting with '%s'\n", (unsigned long)act->mActions.size(), act->mActions[0].mFunction.c_str());
       }
    }
  else
    {
      m_thread_running = true;
      DataManager::SetValue("tw_action_thread_running", "1");
      pthread_mutex_unlock(&m_act_lock);
      ThreadData *d = new ThreadData(this, act);
      pthread_create(&m_thread, NULL, &ActionThread_work_wrapper, d);
    }
}

void ActionThread::run(void *data)
{
  ThreadData *d = (ThreadData *) data;
  GUIAction *act = d->act;

  std::vector < GUIAction::Action >::iterator it;
  for (it = act->mActions.begin(); it != act->mActions.end(); ++it)
    act->doAction(*it);

  pthread_mutex_lock(&m_act_lock);
  m_thread_running = false;
  DataManager::SetValue("tw_action_thread_running", "0");
  pthread_mutex_unlock(&m_act_lock);
  delete d;
}

GUIAction::GUIAction(xml_node <> *node):GUIObject(node)
{
  xml_node <> *child;
  xml_node <> *actions;
  xml_attribute <> *attr;

  if (!node)
    return;

  if (mf.empty())
    {
#define ADD_ACTION(n) mf[#n] = &GUIAction::n
#define ADD_ACTION_EX(name, func) mf[name] = &GUIAction::func
      // These actions will be run in the caller's thread
      ADD_ACTION(reboot);
      ADD_ACTION(home);
      ADD_ACTION(key);
      ADD_ACTION(page);
      ADD_ACTION(reload);
      ADD_ACTION(check_and_reload);
      ADD_ACTION(readBackup);
      ADD_ACTION(set);
      ADD_ACTION(clear);
      ADD_ACTION(mount);
      ADD_ACTION(unmount);
      ADD_ACTION_EX("umount", unmount);
      ADD_ACTION(restoredefaultsettings);
      ADD_ACTION(copylog);
      ADD_ACTION(compute);
      ADD_ACTION_EX("addsubtract", compute);
      ADD_ACTION(setguitimezone);
      ADD_ACTION(overlay);
      ADD_ACTION(queuezip);
      ADD_ACTION(cancelzip);
      ADD_ACTION(queueclear);
      ADD_ACTION(sleep);
      ADD_ACTION(sleepcounter);
      ADD_ACTION(appenddatetobackupname);
      ADD_ACTION(generatebackupname);
      ADD_ACTION(checkpartitionlist);
      ADD_ACTION(getpartitiondetails);
      ADD_ACTION(screenshot);
      ADD_ACTION_EX("screenshotinternal", screenshot);
      ADD_ACTION(setbrightness);
      ADD_ACTION(fileexists);
      ADD_ACTION(killterminal);
      ADD_ACTION(checkbackupname);
      ADD_ACTION(adbsideloadcancel);
      ADD_ACTION(startmtp);
      ADD_ACTION(stopmtp);
      ADD_ACTION(cancelbackup);
      ADD_ACTION(checkpartitionlifetimewrites);
      ADD_ACTION(mountsystemtoggle);
      ADD_ACTION(setlanguage);
      ADD_ACTION(togglebacklight);
      ADD_ACTION(enableadb);
      ADD_ACTION(enablefastboot);
      ADD_ACTION(changeterminal);
      ADD_ACTION(unmapsuperdevices);
      ADD_ACTION(disableled);
      ADD_ACTION(flashlight);

          //fordownloads actions
      ADD_ACTION(fileextension);
      ADD_ACTION(up_a_level);
      ADD_ACTION(checkbackupfolder);
      ADD_ACTION(calculate_chmod);
      ADD_ACTION(get_chmod);
      ADD_ACTION(set_chmod);
      ADD_ACTION(setpassword);
      ADD_ACTION(passwordcheck);

      // remember actions that run in the caller thread
      for (mapFunc::const_iterator it = mf.begin(); it != mf.end(); ++it)
        setActionsRunningInCallerThread.insert(it->first);

      // These actions will run in a separate thread
      ADD_ACTION(flash);
      ADD_ACTION(wipe);
      ADD_ACTION(refreshsizes);
      ADD_ACTION(nandroid);
      ADD_ACTION(fixcontexts);
      ADD_ACTION(fixpermissions);
      ADD_ACTION(dd);
      ADD_ACTION(partitionsd);
      ADD_ACTION(cmd);
      ADD_ACTION(terminalcommand);
      ADD_ACTION(reinjecttwrp);
      ADD_ACTION(decrypt);
      ADD_ACTION(adbsideload);
      ADD_ACTION(openrecoveryscript);
      ADD_ACTION(installsu);
      ADD_ACTION(fixsu);

      ADD_ACTION(decrypt_backup);
      ADD_ACTION(repair);
      ADD_ACTION(resize);
      ADD_ACTION(changefilesystem);
      ADD_ACTION(flashimage);
      ADD_ACTION(twcmd);
      ADD_ACTION(setbootslot);
      ADD_ACTION(repackimage);
      ADD_ACTION(reflashtwrp);
      ADD_ACTION(fixabrecoverybootloop);
      ADD_ACTION(adb);
      ADD_ACTION(wlfw);
      ADD_ACTION(wlfx);
      ADD_ACTION(calldeactivateprocess);
      ADD_ACTION(disable_replace);
#ifdef FOX_USE_NANO_EDITOR
      ADD_ACTION(editfile);
#endif
      ADD_ACTION(mergesnapshots);
      ADD_ACTION(disableAVB2);

      //[f/d] Threaded actions
      ADD_ACTION(batch);
      ADD_ACTION(generatedigests);
      ADD_ACTION(ftls); //ftls (foxtools) - silent cmd
   }

  // First, get the action
  actions = FindNode(node, "actions");
  if (actions)
    child = FindNode(actions, "action");
  else
    child = FindNode(node, "action");

  if (!child)
    return;

  while (child)
    {
      Action action;

      attr = child->first_attribute("function");
      if (!attr)
        return;

      action.mFunction = attr->value();
      action.mArg = child->value();
      mActions.push_back(action);

      child = child->next_sibling("action");
    }

  // Now, let's get either the key or region
  child = FindNode(node, "touch");
  if (child)
    {
      attr = child->first_attribute("key");
                  if (!attr) attr = child->first_attribute("hkey");
      if (attr)
        {
          std::vector < std::string > keys =
            TWFunc::Split_String(attr->value(), "+");
          for (size_t i = 0; i < keys.size(); ++i)
            {
              const int key = getKeyByName(keys[i]);
              mKeys[std::string(attr->name()) == "hkey" ? key + 200 : key] = false;
            }
        }
      else
        {
          attr = child->first_attribute("x");
          if (!attr)
            return;
          mActionX = atol(attr->value());
          attr = child->first_attribute("y");
          if (!attr)
            return;
          mActionY = atol(attr->value());
          attr = child->first_attribute("w");
          if (!attr)
            return;
          mActionW = atol(attr->value());
          attr = child->first_attribute("h");
          if (!attr)
            return;
          mActionH = atol(attr->value());
        }
    }
}

int GUIAction::NotifyTouch(TOUCH_STATE state, int x __unused, int y __unused)
{
  if (state == TOUCH_RELEASE)
    doActions();

  return 0;
}


int GUIAction::NotifyKey(int key, bool down)
{
  std::map < int, bool >::iterator itr = mKeys.find(key);
  if (itr == mKeys.end())
    return 1;

  bool prevState = itr->second;
  itr->second = down;

  // If there is only one key for this action, wait for key up so it
  // doesn't trigger with multi-key actions.
  // Else, check if all buttons are pressed, then consume their release events
  // so they don't trigger one-button actions and reset mKeys pressed status
  if (mKeys.size() == 1)
    {
                  if ((!down && prevState) || mime > 500)
        {
          doActions();
                        if (mime) {
#ifndef TW_NO_HAPTICS
                                DataManager::Vibrate("tw_button_vibrate");
#endif
                                mime = 0;
                        }
          return 0;
        }
    }
  else if (down)
    {
      for (itr = mKeys.begin(); itr != mKeys.end(); ++itr)
        {
          if (!itr->second)
            return 1;
        }

      // Passed, all req buttons are pressed, reset them and consume release events
      HardwareKeyboard *kb = PageManager::GetHardwareKeyboard();
      for (itr = mKeys.begin(); itr != mKeys.end(); ++itr)
        {
          kb->ConsumeKeyRelease(itr->first);
          itr->second = false;
        }

      doActions();
      if (mime) {
#ifndef TW_NO_HAPTICS
                          DataManager::Vibrate("tw_button_vibrate");
#endif
                          mime = 0;
                  }
      return 0;
    }

  return 1;
}

int GUIAction::NotifyVarChange(const std::string & varName,
                               const std::string & value)
{
  GUIObject::NotifyVarChange(varName, value);

  if (varName.empty() && !isConditionValid() && mKeys.empty() && !mActionW)
    doActions();
  else if ((varName.empty() || IsConditionVariable(varName))
           && isConditionValid() && isConditionTrue())
    doActions();

  return 0;
}

void GUIAction::simulate_progress_bar(void)
{
  gui_msg("simulating=Simulating actions...");
  for (int i = 0; i < 5; i++)
    {
      if (PartitionManager.stop_backup.get_value())
        {
          DataManager::SetValue("tw_cancel_backup", 1);
          gui_msg("backup_cancel=Backup Cancelled");
          DataManager::SetValue("ui_progress", 0);
          PartitionManager.stop_backup.set_value(0);
          return;
        }
      usleep(500000);
      DataManager::SetValue("ui_progress", i * 20);
    }
}

int GUIAction::flash_zip(std::string filename, int *wipe_cache)
{
  int ret_val = 0;

  DataManager::SetValue("ui_progress", 0);

  DataManager::SetValue("ui_portion_size", 0);
  DataManager::SetValue("ui_portion_start", 0);

  if (filename.empty())
    {
      LOGERR("No file specified.\n");
      return -1;
    }

  if (!TWFunc::Path_Exists(filename))
    {
      if (!PartitionManager.Mount_By_Path(filename, true))
        {
          return -1;
        }
      if (!TWFunc::Path_Exists(filename))
        {
          gui_msg(Msg(msg::kError, "unable_to_locate=Unable to locate {1}.")
                  (filename));
          return -1;
        }
    }

  if (simulate)
    {
      simulate_progress_bar();
    }
  else
    {
        char apex_enabled[PROPERTY_VALUE_MAX];
        property_get("twrp.apex.flattened", apex_enabled, "");
        if (strcmp(apex_enabled, "true") == 0) {
                        umount("/apex");
        }
      ret_val = TWinstall_zip(filename.c_str(), wipe_cache);
      PartitionManager.Unlock_Block_Partitions();

      // Now, check if we need to ensure TWRP remains installed...
      struct stat st;
      if (stat("/system/bin/installTwrp", &st) == 0)
        {
          DataManager::SetValue("tw_operation", "Configuring TWRP");
          DataManager::SetValue("tw_partition", "");
          gui_msg("config_twrp=Configuring TWRP...");
          if (TWFunc::Exec_Cmd("/system/bin/installTwrp reinstall") < 0)
            {
              gui_msg
                ("config_twrp_err=Unable to configure TWRP with this kernel.");
            }
        }

      //* DJ9
      Fox_Zip_Installer_Code = DataManager::GetIntValue(FOX_ZIP_INSTALLER_CODE);
      usleep(32);
      if (Fox_Zip_Installer_Code == 0) // this is a standard zip installer (not a ROM)
        {
           if (DataManager::GetIntValue(FOX_INSTALL_PREBUILT_ZIP) == 1)
              {
                   LOGINFO("OrangeFox: processed internal zip: %s\n",filename.c_str());
              }
              else
                   LOGINFO("OrangeFox: installed standard zip: %s\n",filename.c_str());
        }
      else // this is a ROM install
        {
                LOGINFO("OrangeFox: installed ROM: %s\n",filename.c_str());
        }
       LOGINFO ("flash_zip: installer code = %i\n", DataManager::GetIntValue(FOX_ZIP_INSTALLER_CODE));
      //* DJ9
    }

  // Done
  DataManager::SetValue("ui_progress", 100);
  DataManager::SetValue("ui_progress", 0);
  DataManager::SetValue("ui_portion_size", 0);
  DataManager::SetValue("ui_portion_start", 0);
  return ret_val;
}

GUIAction::ThreadType GUIAction::getThreadType(const GUIAction::
                                               Action & action)
{
  string func = gui_parse_text(action.mFunction);
  bool needsThread =
    setActionsRunningInCallerThread.find(func) ==
    setActionsRunningInCallerThread.end();
  if (needsThread)
    {
      if (func == "cancelbackup")
        return THREAD_CANCEL;
      else
        return THREAD_ACTION;
    }
  return THREAD_NONE;
}

int GUIAction::doActions()
{
  if (mActions.size() < 1)
    return -1;

  // Determine in which thread to run the actions.
  // Do it for all actions at once before starting, so that we can cancel the whole batch if the thread is already busy.
  ThreadType threadType = THREAD_NONE;
  std::vector < Action >::iterator it;
  for (it = mActions.begin(); it != mActions.end(); ++it)
    {
      ThreadType tt = getThreadType(*it);
      if (tt == THREAD_NONE)
        continue;
      if (threadType == THREAD_NONE)
        threadType = tt;
      else if (threadType != tt)
        {
          LOGERR("Can't mix normal and cancel actions in the same list.\n"
                 "Running the whole batch in the cancel thread.\n");
          threadType = THREAD_CANCEL;
          break;
        }
    }

  // Now run the actions in the desired thread.
  switch (threadType)
    {
    case THREAD_ACTION:
      action_thread.threadActions(this);
      break;

    case THREAD_CANCEL:
      cancel_thread.threadActions(this);
      break;

    default:
      {
        // no iterators here because theme reloading might kill our object
        const size_t cnt = mActions.size();
        for (size_t i = 0; i < cnt; ++i)
          doAction(mActions[i]);
      }
    }

  return 0;
}

int GUIAction::doAction(Action action)
{
  DataManager::GetValue(TW_SIMULATE_ACTIONS, simulate);

  std::string function = gui_parse_text(action.mFunction);
  std::string arg = gui_parse_text(action.mArg);

  // find function and execute it
  mapFunc::const_iterator funcitr = mf.find(function);
  if (funcitr != mf.end())
    return (this->*funcitr->second) (arg);

  if (! Hide_Reboot_Kludge_Fix(function))
  LOGERR("Unknown action '%s'\n", function.c_str());
  return -1;
}

void GUIAction::operation_start(const string operation_name)
{
        LOGINFO("operation_start: '%s'\n", operation_name.c_str());
        time(&Start);
        DataManager::SetValue(TW_ACTION_BUSY, 1);
        DataManager::SetValue("ui_progress", 0);
        DataManager::SetValue("ui_portion_size", 0);
        DataManager::SetValue("ui_portion_start", 0);
        DataManager::SetValue("tw_operation", operation_name);
        DataManager::SetValue("tw_operation_state", 0);
        DataManager::SetValue("tw_operation_status", 0);
        bool tw_ab_device = TWFunc::get_log_dir() != CACHE_LOGS_DIR;
        DataManager::SetValue("tw_ab_device", tw_ab_device);
}

void GUIAction::operation_end(const int operation_status)
{
        time_t Stop;
        int simulate_fail;
        DataManager::SetValue("ui_progress", 100);
        if (simulate) {
                DataManager::GetValue(TW_SIMULATE_FAIL, simulate_fail);
                if (simulate_fail != 0)
                        DataManager::SetValue("tw_operation_status", 1);
                else
                        DataManager::SetValue("tw_operation_status", 0);
        } else {
                if (operation_status != 0) {
                        DataManager::SetValue("tw_operation_status", 1);
                }
                else {
                        DataManager::SetValue("tw_operation_status", 0);
                }
        }
        DataManager::SetValue("tw_operation_state", 1);
        DataManager::SetValue(TW_ACTION_BUSY, 0);
        blankTimer.resetTimerAndUnblank();
        property_set("orangefox.action_complete", "1");
        time(&Stop);

#ifndef TW_NO_HAPTICS
        if ((int) difftime(Stop, Start) > 10)
                DataManager::Vibrate("tw_action_vibrate");
#endif

        LOGINFO("operation_end - status=%d\n", operation_status);
}

int GUIAction::reboot(std::string arg)
{
  sync();
  DataManager::SetValue("tw_gui_done", 1);
  DataManager::SetValue("tw_reboot_arg", arg);
  return 0;
}

int GUIAction::home(std::string arg __unused)
{
  gui_changePage("main");
  return 0;
}

int GUIAction::key(std::string arg)
{
  const int key = getKeyByName(arg)